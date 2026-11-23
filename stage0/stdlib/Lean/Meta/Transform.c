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
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_zetaReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_zetaReduce___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_zetaReduce___closed__0 = (const lean_object*)&l_Lean_Meta_zetaReduce___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_1103_; uint16_t v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v___y_1119_; lean_object* v_toCold_1124_; lean_object* v_currRecDepth_1125_; lean_object* v_ref_1126_; uint16_t v_optionFlags_1127_; uint8_t v_suppressElabErrors_1128_; uint8_t v_checkDeprecated_1129_; uint8_t v_isRecordingDeps_1130_; lean_object* v_maxRecDepth_1131_; lean_object* v_cancelTk_x3f_1132_; 
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
v___x_1121_ = lean_nat_add(v___y_1117_, v___x_1120_);
lean_inc_ref(v___y_1118_);
v___x_1122_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1122_, 0, v___y_1118_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
lean_ctor_set(v___x_1122_, 2, v___y_1114_);
lean_ctor_set_uint16(v___x_1122_, sizeof(void*)*3, v___y_1113_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 2, v___y_1115_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 3, v___y_1116_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 4, v___y_1119_);
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
v___y_1113_ = v_optionFlags_1127_;
v___y_1114_ = v_ref_1126_;
v___y_1115_ = v_suppressElabErrors_1128_;
v___y_1116_ = v_checkDeprecated_1129_;
v___y_1117_ = v_currRecDepth_1125_;
v___y_1118_ = v_toCold_1124_;
v___y_1119_ = v_isRecordingDeps_1130_;
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
v___y_1113_ = v_optionFlags_1127_;
v___y_1114_ = v_ref_1126_;
v___y_1115_ = v_suppressElabErrors_1128_;
v___y_1116_ = v_checkDeprecated_1129_;
v___y_1117_ = v_currRecDepth_1125_;
v___y_1118_ = v_toCold_1124_;
v___y_1119_ = v_isRecordingDeps_1130_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v_declName_1826_, lean_object* v_a_1827_, lean_object* v___f_1828_, uint8_t v_nondep_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
uint8_t v___x_1832_; lean_object* v___x_3461__overap_1833_; lean_object* v___x_1834_; 
v___x_1832_ = 0;
v___x_3461__overap_1833_ = l_Lean_Meta_withLetDecl___redArg(v___x_1824_, v___x_1825_, v_declName_1826_, v_a_1827_, v_a_1831_, v___f_1828_, v_nondep_1829_, v___x_1832_);
lean_inc(v_a_1830_);
v___x_1834_ = lean_apply_1(v___x_3461__overap_1833_, v_a_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1835_, lean_object* v___x_1836_, lean_object* v_declName_1837_, lean_object* v_a_1838_, lean_object* v___f_1839_, lean_object* v_nondep_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
uint8_t v_nondep_3570__boxed_1843_; lean_object* v_res_1844_; 
v_nondep_3570__boxed_1843_ = lean_unbox(v_nondep_1840_);
v_res_1844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1835_, v___x_1836_, v_declName_1837_, v_a_1838_, v___f_1839_, v_nondep_3570__boxed_1843_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1845_, uint8_t v_usedLetOnly_1846_, lean_object* v_inst_1847_, lean_object* v_toBind_1848_, lean_object* v___f_1849_, lean_object* v_a_1850_){
_start:
{
uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1851_ = 0;
v___x_1852_ = 1;
v___x_1853_ = lean_box(v_usedLetOnly_1846_);
v___x_1854_ = lean_box(v___x_1851_);
v___x_1855_ = lean_box(v___x_1852_);
v___x_1856_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1856_, 0, v_fvars_1845_);
lean_closure_set(v___x_1856_, 1, v_a_1850_);
lean_closure_set(v___x_1856_, 2, v___x_1853_);
lean_closure_set(v___x_1856_, 3, v___x_1854_);
lean_closure_set(v___x_1856_, 4, v___x_1855_);
v___x_1857_ = lean_apply_2(v_inst_1847_, lean_box(0), v___x_1856_);
v___x_1858_ = lean_apply_4(v_toBind_1848_, lean_box(0), lean_box(0), v___x_1857_, v___f_1849_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1859_, lean_object* v_usedLetOnly_1860_, lean_object* v_inst_1861_, lean_object* v_toBind_1862_, lean_object* v___f_1863_, lean_object* v_a_1864_){
_start:
{
uint8_t v_usedLetOnly_boxed_1865_; lean_object* v_res_1866_; 
v_usedLetOnly_boxed_1865_ = lean_unbox(v_usedLetOnly_1860_);
v_res_1866_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1859_, v_usedLetOnly_boxed_1865_, v_inst_1861_, v_toBind_1862_, v___f_1863_, v_a_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1867_, uint8_t v_usedLetOnly_1868_, lean_object* v_inst_1869_, lean_object* v_toBind_1870_, lean_object* v___f_1871_, lean_object* v_a_1872_){
_start:
{
uint8_t v___x_1873_; uint8_t v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1873_ = 0;
v___x_1874_ = 1;
v___x_1875_ = 1;
v___x_1876_ = lean_box(v___x_1873_);
v___x_1877_ = lean_box(v_usedLetOnly_1868_);
v___x_1878_ = lean_box(v___x_1873_);
v___x_1879_ = lean_box(v___x_1874_);
v___x_1880_ = lean_box(v___x_1875_);
v___x_1881_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1881_, 0, v_fvars_1867_);
lean_closure_set(v___x_1881_, 1, v_a_1872_);
lean_closure_set(v___x_1881_, 2, v___x_1876_);
lean_closure_set(v___x_1881_, 3, v___x_1877_);
lean_closure_set(v___x_1881_, 4, v___x_1878_);
lean_closure_set(v___x_1881_, 5, v___x_1879_);
lean_closure_set(v___x_1881_, 6, v___x_1880_);
v___x_1882_ = lean_apply_2(v_inst_1869_, lean_box(0), v___x_1881_);
v___x_1883_ = lean_apply_4(v_toBind_1870_, lean_box(0), lean_box(0), v___x_1882_, v___f_1871_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1884_, lean_object* v_usedLetOnly_1885_, lean_object* v_inst_1886_, lean_object* v_toBind_1887_, lean_object* v___f_1888_, lean_object* v_a_1889_){
_start:
{
uint8_t v_usedLetOnly_boxed_1890_; lean_object* v_res_1891_; 
v_usedLetOnly_boxed_1890_ = lean_unbox(v_usedLetOnly_1885_);
v_res_1891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1884_, v_usedLetOnly_boxed_1890_, v_inst_1886_, v_toBind_1887_, v___f_1888_, v_a_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v_binderName_1894_, uint8_t v_binderInfo_1895_, lean_object* v___f_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v___x_1899_; lean_object* v___x_3519__overap_1900_; lean_object* v___x_1901_; 
v___x_1899_ = 0;
v___x_3519__overap_1900_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1892_, v___x_1893_, v_binderName_1894_, v_binderInfo_1895_, v_a_1898_, v___f_1896_, v___x_1899_);
lean_inc(v_a_1897_);
v___x_1901_ = lean_apply_1(v___x_3519__overap_1900_, v_a_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1902_, lean_object* v___x_1903_, lean_object* v_binderName_1904_, lean_object* v_binderInfo_1905_, lean_object* v___f_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
uint8_t v_binderInfo_3638__boxed_1909_; lean_object* v_res_1910_; 
v_binderInfo_3638__boxed_1909_ = lean_unbox(v_binderInfo_1905_);
v_res_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1902_, v___x_1903_, v_binderName_1904_, v_binderInfo_3638__boxed_1909_, v___f_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_f_1911_, lean_object* v_postApp_1912_, lean_object* v___y_1913_, lean_object* v_toBind_1914_, lean_object* v___f_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = l_Lean_mkAppN(v_f_1911_, v_a_1916_);
v___x_1918_ = lean_apply_2(v_postApp_1912_, v___y_1913_, v___x_1917_);
v___x_1919_ = lean_apply_4(v_toBind_1914_, lean_box(0), lean_box(0), v___x_1918_, v___f_1915_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_f_1920_, lean_object* v_postApp_1921_, lean_object* v___y_1922_, lean_object* v_toBind_1923_, lean_object* v___f_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_f_1920_, v_postApp_1921_, v___y_1922_, v_toBind_1923_, v___f_1924_, v_a_1925_);
lean_dec_ref(v_a_1925_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v_toApplicative_1927_, lean_object* v_next_1928_, lean_object* v_G_1929_, lean_object* v___y_1930_, lean_object* v_a_1931_){
_start:
{
if (lean_obj_tag(v_a_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_toPure_1933_; lean_object* v___x_1934_; 
lean_dec(v_G_1929_);
v_a_1932_ = lean_ctor_get(v_a_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v_a_1931_, 1);
v_toPure_1933_ = lean_ctor_get(v_toApplicative_1927_, 1);
lean_inc(v_toPure_1933_);
lean_dec_ref(v_toApplicative_1927_);
v___x_1934_ = lean_apply_2(v_toPure_1933_, lean_box(0), v_a_1932_);
return v___x_1934_;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec_ref(v_toApplicative_1927_);
v_a_1935_ = lean_ctor_get(v_a_1931_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v_a_1931_, 1);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_add(v_next_1928_, v___x_1936_);
lean_inc(v___y_1930_);
v___x_1938_ = lean_apply_5(v_G_1929_, v___x_1937_, v_a_1935_, lean_box(0), lean_box(0), v___y_1930_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_1939_, lean_object* v_next_1940_, lean_object* v_G_1941_, lean_object* v___y_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v_toApplicative_1939_, v_next_1940_, v_G_1941_, v___y_1942_, v_a_1943_);
lean_dec(v___y_1942_);
lean_dec(v_next_1940_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1945_, lean_object* v_acc_1946_, lean_object* v_next_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_toPure_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_toPure_1949_ = lean_ctor_get(v_toApplicative_1945_, 1);
lean_inc(v_toPure_1949_);
lean_dec_ref(v_toApplicative_1945_);
v___x_1950_ = lean_array_fset(v_acc_1946_, v_next_1947_, v_a_1948_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
v___x_1952_ = lean_apply_2(v_toPure_1949_, lean_box(0), v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_1953_, lean_object* v_acc_1954_, lean_object* v_next_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_1953_, v_acc_1954_, v_next_1955_, v_a_1956_);
lean_dec(v_next_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v___f_1958_, lean_object* v___y_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1961_; 
lean_inc(v___y_1959_);
v___x_1961_ = lean_apply_2(v___f_1958_, v_a_1960_, v___y_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v___f_1962_, lean_object* v___y_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v___f_1962_, v___y_1963_, v_a_1964_);
lean_dec(v___y_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1966_, uint8_t v_usedLetOnly_1967_, lean_object* v_inst_1968_, lean_object* v_toBind_1969_, lean_object* v___f_1970_, lean_object* v_a_1971_){
_start:
{
uint8_t v___x_1972_; uint8_t v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1972_ = 0;
v___x_1973_ = 1;
v___x_1974_ = 1;
v___x_1975_ = lean_box(v___x_1972_);
v___x_1976_ = lean_box(v_usedLetOnly_1967_);
v___x_1977_ = lean_box(v___x_1973_);
v___x_1978_ = lean_box(v___x_1974_);
v___x_1979_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1979_, 0, v_fvars_1966_);
lean_closure_set(v___x_1979_, 1, v_a_1971_);
lean_closure_set(v___x_1979_, 2, v___x_1975_);
lean_closure_set(v___x_1979_, 3, v___x_1976_);
lean_closure_set(v___x_1979_, 4, v___x_1977_);
lean_closure_set(v___x_1979_, 5, v___x_1978_);
v___x_1980_ = lean_apply_2(v_inst_1968_, lean_box(0), v___x_1979_);
v___x_1981_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1980_, v___f_1970_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1982_, lean_object* v_usedLetOnly_1983_, lean_object* v_inst_1984_, lean_object* v_toBind_1985_, lean_object* v___f_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v_usedLetOnly_boxed_1988_; lean_object* v_res_1989_; 
v_usedLetOnly_boxed_1988_ = lean_unbox(v_usedLetOnly_1983_);
v_res_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1982_, v_usedLetOnly_boxed_1988_, v_inst_1984_, v_toBind_1985_, v___f_1986_, v_a_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v___x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Core_checkSystem(v___x_1990_, v___y_1993_, v___y_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v___x_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v___x_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15(lean_object* v_inst_2006_, lean_object* v_x_2007_, lean_object* v___x_2008_, lean_object* v___x_2009_, lean_object* v_inst_2010_, lean_object* v___f_2011_, lean_object* v___x_2012_, lean_object* v___x_2013_, lean_object* v_a_2014_, lean_object* v_toBind_2015_, lean_object* v___f_2016_, lean_object* v_toApplicative_2017_, lean_object* v_a_2018_){
_start:
{
if (lean_obj_tag(v_a_2018_) == 0)
{
lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_3442__overap_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v_toApplicative_2017_);
v___f_2019_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0));
v___x_2020_ = lean_apply_2(v_inst_2006_, lean_box(0), v___f_2019_);
lean_inc_ref(v___x_2009_);
lean_inc_ref(v___x_2008_);
v___x_2021_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_2021_, 0, lean_box(0));
lean_closure_set(v___x_2021_, 1, lean_box(0));
lean_closure_set(v___x_2021_, 2, lean_box(0));
lean_closure_set(v___x_2021_, 3, lean_box(0));
lean_closure_set(v___x_2021_, 4, v_x_2007_);
lean_closure_set(v___x_2021_, 5, v___x_2008_);
lean_closure_set(v___x_2021_, 6, v___x_2009_);
lean_closure_set(v___x_2021_, 7, lean_box(0));
lean_closure_set(v___x_2021_, 8, v___x_2020_);
v___x_2022_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_2022_, 0, lean_box(0));
lean_closure_set(v___x_2022_, 1, lean_box(0));
lean_closure_set(v___x_2022_, 2, lean_box(0));
lean_closure_set(v___x_2022_, 3, lean_box(0));
lean_closure_set(v___x_2022_, 4, v_x_2007_);
lean_closure_set(v___x_2022_, 5, v___x_2008_);
lean_closure_set(v___x_2022_, 6, v___x_2009_);
lean_closure_set(v___x_2022_, 7, v_inst_2010_);
lean_closure_set(v___x_2022_, 8, lean_box(0));
lean_closure_set(v___x_2022_, 9, lean_box(0));
lean_closure_set(v___x_2022_, 10, v___x_2021_);
lean_closure_set(v___x_2022_, 11, v___f_2011_);
v___x_3442__overap_2023_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_2012_, v___x_2013_, v___x_2022_);
lean_inc(v_a_2014_);
v___x_2024_ = lean_apply_1(v___x_3442__overap_2023_, v_a_2014_);
v___x_2025_ = lean_apply_4(v_toBind_2015_, lean_box(0), lean_box(0), v___x_2024_, v___f_2016_);
return v___x_2025_;
}
else
{
lean_object* v_val_2026_; lean_object* v_toPure_2027_; lean_object* v___x_2028_; 
lean_dec(v___f_2016_);
lean_dec(v_toBind_2015_);
lean_dec_ref(v___x_2013_);
lean_dec_ref(v___x_2012_);
lean_dec(v___f_2011_);
lean_dec_ref(v_inst_2010_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2008_);
lean_dec(v_inst_2006_);
v_val_2026_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v_a_2018_, 1);
v_toPure_2027_ = lean_ctor_get(v_toApplicative_2017_, 1);
lean_inc(v_toPure_2027_);
lean_dec_ref(v_toApplicative_2017_);
v___x_2028_ = lean_apply_2(v_toPure_2027_, lean_box(0), v_val_2026_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___boxed(lean_object* v_inst_2029_, lean_object* v_x_2030_, lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v_inst_2033_, lean_object* v___f_2034_, lean_object* v___x_2035_, lean_object* v___x_2036_, lean_object* v_a_2037_, lean_object* v_toBind_2038_, lean_object* v___f_2039_, lean_object* v_toApplicative_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15(v_inst_2029_, v_x_2030_, v___x_2031_, v___x_2032_, v_inst_2033_, v___f_2034_, v___x_2035_, v___x_2036_, v_a_2037_, v_toBind_2038_, v___f_2039_, v_toApplicative_2040_, v_a_2041_);
lean_dec(v_a_2037_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_pre_2049_, lean_object* v_post_2050_, uint8_t v_usedLetOnly_2051_, uint8_t v_skipConstInApp_2052_, uint8_t v_skipInstances_2053_, lean_object* v_postApp_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_body_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_array_push(v_fvars_2045_, v_x_2058_);
v___x_2061_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2046_, v_inst_2047_, v_inst_2048_, v_pre_2049_, v_post_2050_, v_usedLetOnly_2051_, v_skipConstInApp_2052_, v_skipInstances_2053_, v_postApp_2054_, v_x_2055_, v_x_2056_, v___x_2060_, v_body_2057_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_pre_2066_, lean_object* v_post_2067_, lean_object* v_usedLetOnly_2068_, lean_object* v_skipConstInApp_2069_, lean_object* v_skipInstances_2070_, lean_object* v_postApp_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_body_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v_usedLetOnly_boxed_2077_; uint8_t v_skipConstInApp_boxed_2078_; uint8_t v_skipInstances_boxed_2079_; lean_object* v_res_2080_; 
v_usedLetOnly_boxed_2077_ = lean_unbox(v_usedLetOnly_2068_);
v_skipConstInApp_boxed_2078_ = lean_unbox(v_skipConstInApp_2069_);
v_skipInstances_boxed_2079_ = lean_unbox(v_skipInstances_2070_);
v_res_2080_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2062_, v_inst_2063_, v_inst_2064_, v_inst_2065_, v_pre_2066_, v_post_2067_, v_usedLetOnly_boxed_2077_, v_skipConstInApp_boxed_2078_, v_skipInstances_boxed_2079_, v_postApp_2071_, v_x_2072_, v_x_2073_, v_body_2074_, v_x_2075_, v___y_2076_);
lean_dec(v___y_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_pre_2084_, lean_object* v_post_2085_, uint8_t v_usedLetOnly_2086_, uint8_t v_skipConstInApp_2087_, uint8_t v_skipInstances_2088_, lean_object* v_postApp_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2081_, v_inst_2082_, v_inst_2083_, v_pre_2084_, v_post_2085_, v_usedLetOnly_2086_, v_skipConstInApp_2087_, v_skipInstances_2088_, v_postApp_2089_, v_x_2090_, v_x_2091_, v_a_2093_, v_a_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_pre_2098_, lean_object* v_post_2099_, lean_object* v_usedLetOnly_2100_, lean_object* v_skipConstInApp_2101_, lean_object* v_skipInstances_2102_, lean_object* v_postApp_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
uint8_t v_usedLetOnly_boxed_2108_; uint8_t v_skipConstInApp_boxed_2109_; uint8_t v_skipInstances_boxed_2110_; lean_object* v_res_2111_; 
v_usedLetOnly_boxed_2108_ = lean_unbox(v_usedLetOnly_2100_);
v_skipConstInApp_boxed_2109_ = lean_unbox(v_skipConstInApp_2101_);
v_skipInstances_boxed_2110_ = lean_unbox(v_skipInstances_2102_);
v_res_2111_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2095_, v_inst_2096_, v_inst_2097_, v_pre_2098_, v_post_2099_, v_usedLetOnly_boxed_2108_, v_skipConstInApp_boxed_2109_, v_skipInstances_boxed_2110_, v_postApp_2103_, v_x_2104_, v_x_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2106_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_pre_2115_, lean_object* v_post_2116_, uint8_t v_usedLetOnly_2117_, uint8_t v_skipConstInApp_2118_, uint8_t v_skipInstances_2119_, lean_object* v_postApp_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_fvars_2123_, lean_object* v_e_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2112_);
v___x_2128_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2121_, v___x_2126_, v___x_2127_, v_inst_2112_);
v___x_2129_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2121_, v___x_2126_, v___x_2127_);
lean_inc_ref_n(v_inst_2114_, 2);
lean_inc_ref(v___x_2129_);
v___f_2130_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2130_, 0, v___x_2129_);
lean_closure_set(v___f_2130_, 1, v_inst_2114_);
v___f_2131_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2131_, 0, v___x_2129_);
lean_closure_set(v___f_2131_, 1, v_inst_2114_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___f_2130_);
lean_ctor_set(v___x_2132_, 1, v___f_2131_);
if (lean_obj_tag(v_e_2124_) == 7)
{
lean_object* v_binderName_2133_; lean_object* v_binderType_2134_; lean_object* v_body_2135_; uint8_t v_binderInfo_2136_; lean_object* v_toBind_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___f_2141_; lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_binderName_2133_ = lean_ctor_get(v_e_2124_, 0);
lean_inc(v_binderName_2133_);
v_binderType_2134_ = lean_ctor_get(v_e_2124_, 1);
lean_inc_ref(v_binderType_2134_);
v_body_2135_ = lean_ctor_get(v_e_2124_, 2);
lean_inc_ref(v_body_2135_);
v_binderInfo_2136_ = lean_ctor_get_uint8(v_e_2124_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2124_, 3);
v_toBind_2137_ = lean_ctor_get(v_inst_2112_, 1);
lean_inc(v_toBind_2137_);
v___x_2138_ = lean_box(v_usedLetOnly_2117_);
v___x_2139_ = lean_box(v_skipConstInApp_2118_);
v___x_2140_ = lean_box(v_skipInstances_2119_);
lean_inc(v_x_2122_);
lean_inc(v_postApp_2120_);
lean_inc(v_post_2116_);
lean_inc(v_pre_2115_);
lean_inc_ref(v_inst_2114_);
lean_inc(v_inst_2113_);
lean_inc_ref(v_inst_2112_);
lean_inc_ref(v_fvars_2123_);
v___f_2141_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2141_, 0, v_fvars_2123_);
lean_closure_set(v___f_2141_, 1, v_inst_2112_);
lean_closure_set(v___f_2141_, 2, v_inst_2113_);
lean_closure_set(v___f_2141_, 3, v_inst_2114_);
lean_closure_set(v___f_2141_, 4, v_pre_2115_);
lean_closure_set(v___f_2141_, 5, v_post_2116_);
lean_closure_set(v___f_2141_, 6, v___x_2138_);
lean_closure_set(v___f_2141_, 7, v___x_2139_);
lean_closure_set(v___f_2141_, 8, v___x_2140_);
lean_closure_set(v___f_2141_, 9, v_postApp_2120_);
lean_closure_set(v___f_2141_, 10, v_x_2121_);
lean_closure_set(v___f_2141_, 11, v_x_2122_);
lean_closure_set(v___f_2141_, 12, v_body_2135_);
v___x_2142_ = lean_box(v_binderInfo_2136_);
lean_inc(v_a_2125_);
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2143_, 0, v___x_2132_);
lean_closure_set(v___f_2143_, 1, v___x_2128_);
lean_closure_set(v___f_2143_, 2, v_binderName_2133_);
lean_closure_set(v___f_2143_, 3, v___x_2142_);
lean_closure_set(v___f_2143_, 4, v___f_2141_);
lean_closure_set(v___f_2143_, 5, v_a_2125_);
v___x_2144_ = lean_expr_instantiate_rev(v_binderType_2134_, v_fvars_2123_);
lean_dec_ref(v_fvars_2123_);
lean_dec_ref(v_binderType_2134_);
v___x_2145_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2112_, v_inst_2113_, v_inst_2114_, v_pre_2115_, v_post_2116_, v_usedLetOnly_2117_, v_skipConstInApp_2118_, v_skipInstances_2119_, v_postApp_2120_, v_x_2121_, v_x_2122_, v___x_2144_, v_a_2125_);
v___x_2146_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2145_, v___f_2143_);
return v___x_2146_;
}
else
{
lean_object* v_toBind_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec_ref_known(v___x_2132_, 2);
lean_dec_ref(v___x_2128_);
v_toBind_2147_ = lean_ctor_get(v_inst_2112_, 1);
lean_inc_n(v_toBind_2147_, 2);
v___x_2148_ = lean_box(v_usedLetOnly_2117_);
v___x_2149_ = lean_box(v_skipConstInApp_2118_);
v___x_2150_ = lean_box(v_skipInstances_2119_);
lean_inc(v_a_2125_);
lean_inc(v_x_2122_);
lean_inc(v_postApp_2120_);
lean_inc(v_post_2116_);
lean_inc(v_pre_2115_);
lean_inc_ref(v_inst_2114_);
lean_inc_n(v_inst_2113_, 2);
lean_inc_ref(v_inst_2112_);
v___f_2151_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2151_, 0, v_inst_2112_);
lean_closure_set(v___f_2151_, 1, v_inst_2113_);
lean_closure_set(v___f_2151_, 2, v_inst_2114_);
lean_closure_set(v___f_2151_, 3, v_pre_2115_);
lean_closure_set(v___f_2151_, 4, v_post_2116_);
lean_closure_set(v___f_2151_, 5, v___x_2148_);
lean_closure_set(v___f_2151_, 6, v___x_2149_);
lean_closure_set(v___f_2151_, 7, v___x_2150_);
lean_closure_set(v___f_2151_, 8, v_postApp_2120_);
lean_closure_set(v___f_2151_, 9, v_x_2121_);
lean_closure_set(v___f_2151_, 10, v_x_2122_);
lean_closure_set(v___f_2151_, 11, v_a_2125_);
v___x_2152_ = lean_box(v_usedLetOnly_2117_);
lean_inc_ref(v_fvars_2123_);
v___f_2153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2153_, 0, v_fvars_2123_);
lean_closure_set(v___f_2153_, 1, v___x_2152_);
lean_closure_set(v___f_2153_, 2, v_inst_2113_);
lean_closure_set(v___f_2153_, 3, v_toBind_2147_);
lean_closure_set(v___f_2153_, 4, v___f_2151_);
v___x_2154_ = lean_expr_instantiate_rev(v_e_2124_, v_fvars_2123_);
lean_dec_ref(v_fvars_2123_);
lean_dec_ref(v_e_2124_);
v___x_2155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2112_, v_inst_2113_, v_inst_2114_, v_pre_2115_, v_post_2116_, v_usedLetOnly_2117_, v_skipConstInApp_2118_, v_skipInstances_2119_, v_postApp_2120_, v_x_2121_, v_x_2122_, v___x_2154_, v_a_2125_);
v___x_2156_ = lean_apply_4(v_toBind_2147_, lean_box(0), lean_box(0), v___x_2155_, v___f_2153_);
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_pre_2161_, lean_object* v_post_2162_, uint8_t v_usedLetOnly_2163_, uint8_t v_skipConstInApp_2164_, uint8_t v_skipInstances_2165_, lean_object* v_postApp_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_body_2169_, lean_object* v_x_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_array_push(v_fvars_2157_, v_x_2170_);
v___x_2173_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2158_, v_inst_2159_, v_inst_2160_, v_pre_2161_, v_post_2162_, v_usedLetOnly_2163_, v_skipConstInApp_2164_, v_skipInstances_2165_, v_postApp_2166_, v_x_2167_, v_x_2168_, v___x_2172_, v_body_2169_, v___y_2171_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_pre_2178_, lean_object* v_post_2179_, lean_object* v_usedLetOnly_2180_, lean_object* v_skipConstInApp_2181_, lean_object* v_skipInstances_2182_, lean_object* v_postApp_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v_body_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v_usedLetOnly_boxed_2189_; uint8_t v_skipConstInApp_boxed_2190_; uint8_t v_skipInstances_boxed_2191_; lean_object* v_res_2192_; 
v_usedLetOnly_boxed_2189_ = lean_unbox(v_usedLetOnly_2180_);
v_skipConstInApp_boxed_2190_ = lean_unbox(v_skipConstInApp_2181_);
v_skipInstances_boxed_2191_ = lean_unbox(v_skipInstances_2182_);
v_res_2192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2174_, v_inst_2175_, v_inst_2176_, v_inst_2177_, v_pre_2178_, v_post_2179_, v_usedLetOnly_boxed_2189_, v_skipConstInApp_boxed_2190_, v_skipInstances_boxed_2191_, v_postApp_2183_, v_x_2184_, v_x_2185_, v_body_2186_, v_x_2187_, v___y_2188_);
lean_dec(v___y_2188_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_, lean_object* v_pre_2196_, lean_object* v_post_2197_, uint8_t v_usedLetOnly_2198_, uint8_t v_skipConstInApp_2199_, uint8_t v_skipInstances_2200_, lean_object* v_postApp_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_fvars_2204_, lean_object* v_e_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; 
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2193_);
v___x_2209_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2202_, v___x_2207_, v___x_2208_, v_inst_2193_);
v___x_2210_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2202_, v___x_2207_, v___x_2208_);
lean_inc_ref_n(v_inst_2195_, 2);
lean_inc_ref(v___x_2210_);
v___f_2211_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2211_, 0, v___x_2210_);
lean_closure_set(v___f_2211_, 1, v_inst_2195_);
v___f_2212_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2212_, 0, v___x_2210_);
lean_closure_set(v___f_2212_, 1, v_inst_2195_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___f_2211_);
lean_ctor_set(v___x_2213_, 1, v___f_2212_);
if (lean_obj_tag(v_e_2205_) == 6)
{
lean_object* v_binderName_2214_; lean_object* v_binderType_2215_; lean_object* v_body_2216_; uint8_t v_binderInfo_2217_; lean_object* v_toBind_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v_binderName_2214_ = lean_ctor_get(v_e_2205_, 0);
lean_inc(v_binderName_2214_);
v_binderType_2215_ = lean_ctor_get(v_e_2205_, 1);
lean_inc_ref(v_binderType_2215_);
v_body_2216_ = lean_ctor_get(v_e_2205_, 2);
lean_inc_ref(v_body_2216_);
v_binderInfo_2217_ = lean_ctor_get_uint8(v_e_2205_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2205_, 3);
v_toBind_2218_ = lean_ctor_get(v_inst_2193_, 1);
lean_inc(v_toBind_2218_);
v___x_2219_ = lean_box(v_usedLetOnly_2198_);
v___x_2220_ = lean_box(v_skipConstInApp_2199_);
v___x_2221_ = lean_box(v_skipInstances_2200_);
lean_inc(v_x_2203_);
lean_inc(v_postApp_2201_);
lean_inc(v_post_2197_);
lean_inc(v_pre_2196_);
lean_inc_ref(v_inst_2195_);
lean_inc(v_inst_2194_);
lean_inc_ref(v_inst_2193_);
lean_inc_ref(v_fvars_2204_);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2222_, 0, v_fvars_2204_);
lean_closure_set(v___f_2222_, 1, v_inst_2193_);
lean_closure_set(v___f_2222_, 2, v_inst_2194_);
lean_closure_set(v___f_2222_, 3, v_inst_2195_);
lean_closure_set(v___f_2222_, 4, v_pre_2196_);
lean_closure_set(v___f_2222_, 5, v_post_2197_);
lean_closure_set(v___f_2222_, 6, v___x_2219_);
lean_closure_set(v___f_2222_, 7, v___x_2220_);
lean_closure_set(v___f_2222_, 8, v___x_2221_);
lean_closure_set(v___f_2222_, 9, v_postApp_2201_);
lean_closure_set(v___f_2222_, 10, v_x_2202_);
lean_closure_set(v___f_2222_, 11, v_x_2203_);
lean_closure_set(v___f_2222_, 12, v_body_2216_);
v___x_2223_ = lean_box(v_binderInfo_2217_);
lean_inc(v_a_2206_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2224_, 0, v___x_2213_);
lean_closure_set(v___f_2224_, 1, v___x_2209_);
lean_closure_set(v___f_2224_, 2, v_binderName_2214_);
lean_closure_set(v___f_2224_, 3, v___x_2223_);
lean_closure_set(v___f_2224_, 4, v___f_2222_);
lean_closure_set(v___f_2224_, 5, v_a_2206_);
v___x_2225_ = lean_expr_instantiate_rev(v_binderType_2215_, v_fvars_2204_);
lean_dec_ref(v_fvars_2204_);
lean_dec_ref(v_binderType_2215_);
v___x_2226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2193_, v_inst_2194_, v_inst_2195_, v_pre_2196_, v_post_2197_, v_usedLetOnly_2198_, v_skipConstInApp_2199_, v_skipInstances_2200_, v_postApp_2201_, v_x_2202_, v_x_2203_, v___x_2225_, v_a_2206_);
v___x_2227_ = lean_apply_4(v_toBind_2218_, lean_box(0), lean_box(0), v___x_2226_, v___f_2224_);
return v___x_2227_;
}
else
{
lean_object* v_toBind_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref_known(v___x_2213_, 2);
lean_dec_ref(v___x_2209_);
v_toBind_2228_ = lean_ctor_get(v_inst_2193_, 1);
lean_inc_n(v_toBind_2228_, 2);
v___x_2229_ = lean_box(v_usedLetOnly_2198_);
v___x_2230_ = lean_box(v_skipConstInApp_2199_);
v___x_2231_ = lean_box(v_skipInstances_2200_);
lean_inc(v_a_2206_);
lean_inc(v_x_2203_);
lean_inc(v_postApp_2201_);
lean_inc(v_post_2197_);
lean_inc(v_pre_2196_);
lean_inc_ref(v_inst_2195_);
lean_inc_n(v_inst_2194_, 2);
lean_inc_ref(v_inst_2193_);
v___f_2232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2232_, 0, v_inst_2193_);
lean_closure_set(v___f_2232_, 1, v_inst_2194_);
lean_closure_set(v___f_2232_, 2, v_inst_2195_);
lean_closure_set(v___f_2232_, 3, v_pre_2196_);
lean_closure_set(v___f_2232_, 4, v_post_2197_);
lean_closure_set(v___f_2232_, 5, v___x_2229_);
lean_closure_set(v___f_2232_, 6, v___x_2230_);
lean_closure_set(v___f_2232_, 7, v___x_2231_);
lean_closure_set(v___f_2232_, 8, v_postApp_2201_);
lean_closure_set(v___f_2232_, 9, v_x_2202_);
lean_closure_set(v___f_2232_, 10, v_x_2203_);
lean_closure_set(v___f_2232_, 11, v_a_2206_);
v___x_2233_ = lean_box(v_usedLetOnly_2198_);
lean_inc_ref(v_fvars_2204_);
v___f_2234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2234_, 0, v_fvars_2204_);
lean_closure_set(v___f_2234_, 1, v___x_2233_);
lean_closure_set(v___f_2234_, 2, v_inst_2194_);
lean_closure_set(v___f_2234_, 3, v_toBind_2228_);
lean_closure_set(v___f_2234_, 4, v___f_2232_);
v___x_2235_ = lean_expr_instantiate_rev(v_e_2205_, v_fvars_2204_);
lean_dec_ref(v_fvars_2204_);
lean_dec_ref(v_e_2205_);
v___x_2236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2193_, v_inst_2194_, v_inst_2195_, v_pre_2196_, v_post_2197_, v_usedLetOnly_2198_, v_skipConstInApp_2199_, v_skipInstances_2200_, v_postApp_2201_, v_x_2202_, v_x_2203_, v___x_2235_, v_a_2206_);
v___x_2237_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2236_, v___f_2234_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_pre_2242_, lean_object* v_post_2243_, uint8_t v_usedLetOnly_2244_, uint8_t v_skipConstInApp_2245_, uint8_t v_skipInstances_2246_, lean_object* v_postApp_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_, lean_object* v_body_2250_, lean_object* v_x_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_array_push(v_fvars_2238_, v_x_2251_);
v___x_2254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2239_, v_inst_2240_, v_inst_2241_, v_pre_2242_, v_post_2243_, v_usedLetOnly_2244_, v_skipConstInApp_2245_, v_skipInstances_2246_, v_postApp_2247_, v_x_2248_, v_x_2249_, v___x_2253_, v_body_2250_, v___y_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_pre_2259_, lean_object* v_post_2260_, lean_object* v_usedLetOnly_2261_, lean_object* v_skipConstInApp_2262_, lean_object* v_skipInstances_2263_, lean_object* v_postApp_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_body_2267_, lean_object* v_x_2268_, lean_object* v___y_2269_){
_start:
{
uint8_t v_usedLetOnly_boxed_2270_; uint8_t v_skipConstInApp_boxed_2271_; uint8_t v_skipInstances_boxed_2272_; lean_object* v_res_2273_; 
v_usedLetOnly_boxed_2270_ = lean_unbox(v_usedLetOnly_2261_);
v_skipConstInApp_boxed_2271_ = lean_unbox(v_skipConstInApp_2262_);
v_skipInstances_boxed_2272_ = lean_unbox(v_skipInstances_2263_);
v_res_2273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2255_, v_inst_2256_, v_inst_2257_, v_inst_2258_, v_pre_2259_, v_post_2260_, v_usedLetOnly_boxed_2270_, v_skipConstInApp_boxed_2271_, v_skipInstances_boxed_2272_, v_postApp_2264_, v_x_2265_, v_x_2266_, v_body_2267_, v_x_2268_, v___y_2269_);
lean_dec(v___y_2269_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v_declName_2276_, lean_object* v___f_2277_, uint8_t v_nondep_2278_, lean_object* v_a_2279_, lean_object* v_value_2280_, lean_object* v_fvars_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_pre_2285_, lean_object* v_post_2286_, uint8_t v_usedLetOnly_2287_, uint8_t v_skipConstInApp_2288_, uint8_t v_skipInstances_2289_, lean_object* v_postApp_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_toBind_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2295_ = lean_box(v_nondep_2278_);
lean_inc(v_a_2279_);
v___f_2296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2296_, 0, v___x_2274_);
lean_closure_set(v___f_2296_, 1, v___x_2275_);
lean_closure_set(v___f_2296_, 2, v_declName_2276_);
lean_closure_set(v___f_2296_, 3, v_a_2294_);
lean_closure_set(v___f_2296_, 4, v___f_2277_);
lean_closure_set(v___f_2296_, 5, v___x_2295_);
lean_closure_set(v___f_2296_, 6, v_a_2279_);
v___x_2297_ = lean_expr_instantiate_rev(v_value_2280_, v_fvars_2281_);
v___x_2298_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2282_, v_inst_2283_, v_inst_2284_, v_pre_2285_, v_post_2286_, v_usedLetOnly_2287_, v_skipConstInApp_2288_, v_skipInstances_2289_, v_postApp_2290_, v_x_2291_, v_x_2292_, v___x_2297_, v_a_2279_);
v___x_2299_ = lean_apply_4(v_toBind_2293_, lean_box(0), lean_box(0), v___x_2298_, v___f_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2300_ = _args[0];
lean_object* v___x_2301_ = _args[1];
lean_object* v_declName_2302_ = _args[2];
lean_object* v___f_2303_ = _args[3];
lean_object* v_nondep_2304_ = _args[4];
lean_object* v_a_2305_ = _args[5];
lean_object* v_value_2306_ = _args[6];
lean_object* v_fvars_2307_ = _args[7];
lean_object* v_inst_2308_ = _args[8];
lean_object* v_inst_2309_ = _args[9];
lean_object* v_inst_2310_ = _args[10];
lean_object* v_pre_2311_ = _args[11];
lean_object* v_post_2312_ = _args[12];
lean_object* v_usedLetOnly_2313_ = _args[13];
lean_object* v_skipConstInApp_2314_ = _args[14];
lean_object* v_skipInstances_2315_ = _args[15];
lean_object* v_postApp_2316_ = _args[16];
lean_object* v_x_2317_ = _args[17];
lean_object* v_x_2318_ = _args[18];
lean_object* v_toBind_2319_ = _args[19];
lean_object* v_a_2320_ = _args[20];
_start:
{
uint8_t v_nondep_3862__boxed_2321_; uint8_t v_usedLetOnly_boxed_2322_; uint8_t v_skipConstInApp_boxed_2323_; uint8_t v_skipInstances_boxed_2324_; lean_object* v_res_2325_; 
v_nondep_3862__boxed_2321_ = lean_unbox(v_nondep_2304_);
v_usedLetOnly_boxed_2322_ = lean_unbox(v_usedLetOnly_2313_);
v_skipConstInApp_boxed_2323_ = lean_unbox(v_skipConstInApp_2314_);
v_skipInstances_boxed_2324_ = lean_unbox(v_skipInstances_2315_);
v_res_2325_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2300_, v___x_2301_, v_declName_2302_, v___f_2303_, v_nondep_3862__boxed_2321_, v_a_2305_, v_value_2306_, v_fvars_2307_, v_inst_2308_, v_inst_2309_, v_inst_2310_, v_pre_2311_, v_post_2312_, v_usedLetOnly_boxed_2322_, v_skipConstInApp_boxed_2323_, v_skipInstances_boxed_2324_, v_postApp_2316_, v_x_2317_, v_x_2318_, v_toBind_2319_, v_a_2320_);
lean_dec_ref(v_fvars_2307_);
lean_dec_ref(v_value_2306_);
lean_dec(v_a_2305_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_pre_2329_, lean_object* v_post_2330_, uint8_t v_usedLetOnly_2331_, uint8_t v_skipConstInApp_2332_, uint8_t v_skipInstances_2333_, lean_object* v_postApp_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_fvars_2337_, lean_object* v_e_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___f_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2326_);
v___x_2342_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2335_, v___x_2340_, v___x_2341_, v_inst_2326_);
v___x_2343_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2335_, v___x_2340_, v___x_2341_);
lean_inc_ref_n(v_inst_2328_, 2);
lean_inc_ref(v___x_2343_);
v___f_2344_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2344_, 0, v___x_2343_);
lean_closure_set(v___f_2344_, 1, v_inst_2328_);
v___f_2345_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2345_, 0, v___x_2343_);
lean_closure_set(v___f_2345_, 1, v_inst_2328_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___f_2344_);
lean_ctor_set(v___x_2346_, 1, v___f_2345_);
if (lean_obj_tag(v_e_2338_) == 8)
{
lean_object* v_declName_2347_; lean_object* v_type_2348_; lean_object* v_value_2349_; lean_object* v_body_2350_; uint8_t v_nondep_2351_; lean_object* v_toBind_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_declName_2347_ = lean_ctor_get(v_e_2338_, 0);
lean_inc(v_declName_2347_);
v_type_2348_ = lean_ctor_get(v_e_2338_, 1);
lean_inc_ref(v_type_2348_);
v_value_2349_ = lean_ctor_get(v_e_2338_, 2);
lean_inc_ref(v_value_2349_);
v_body_2350_ = lean_ctor_get(v_e_2338_, 3);
lean_inc_ref(v_body_2350_);
v_nondep_2351_ = lean_ctor_get_uint8(v_e_2338_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2338_, 4);
v_toBind_2352_ = lean_ctor_get(v_inst_2326_, 1);
lean_inc_n(v_toBind_2352_, 2);
v___x_2353_ = lean_box(v_usedLetOnly_2331_);
v___x_2354_ = lean_box(v_skipConstInApp_2332_);
v___x_2355_ = lean_box(v_skipInstances_2333_);
lean_inc_n(v_x_2336_, 2);
lean_inc_n(v_postApp_2334_, 2);
lean_inc_n(v_post_2330_, 2);
lean_inc_n(v_pre_2329_, 2);
lean_inc_ref_n(v_inst_2328_, 2);
lean_inc_n(v_inst_2327_, 2);
lean_inc_ref_n(v_inst_2326_, 2);
lean_inc_ref_n(v_fvars_2337_, 2);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2356_, 0, v_fvars_2337_);
lean_closure_set(v___f_2356_, 1, v_inst_2326_);
lean_closure_set(v___f_2356_, 2, v_inst_2327_);
lean_closure_set(v___f_2356_, 3, v_inst_2328_);
lean_closure_set(v___f_2356_, 4, v_pre_2329_);
lean_closure_set(v___f_2356_, 5, v_post_2330_);
lean_closure_set(v___f_2356_, 6, v___x_2353_);
lean_closure_set(v___f_2356_, 7, v___x_2354_);
lean_closure_set(v___f_2356_, 8, v___x_2355_);
lean_closure_set(v___f_2356_, 9, v_postApp_2334_);
lean_closure_set(v___f_2356_, 10, v_x_2335_);
lean_closure_set(v___f_2356_, 11, v_x_2336_);
lean_closure_set(v___f_2356_, 12, v_body_2350_);
v___x_2357_ = lean_box(v_nondep_2351_);
v___x_2358_ = lean_box(v_usedLetOnly_2331_);
v___x_2359_ = lean_box(v_skipConstInApp_2332_);
v___x_2360_ = lean_box(v_skipInstances_2333_);
lean_inc(v_a_2339_);
v___f_2361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 21, 20);
lean_closure_set(v___f_2361_, 0, v___x_2346_);
lean_closure_set(v___f_2361_, 1, v___x_2342_);
lean_closure_set(v___f_2361_, 2, v_declName_2347_);
lean_closure_set(v___f_2361_, 3, v___f_2356_);
lean_closure_set(v___f_2361_, 4, v___x_2357_);
lean_closure_set(v___f_2361_, 5, v_a_2339_);
lean_closure_set(v___f_2361_, 6, v_value_2349_);
lean_closure_set(v___f_2361_, 7, v_fvars_2337_);
lean_closure_set(v___f_2361_, 8, v_inst_2326_);
lean_closure_set(v___f_2361_, 9, v_inst_2327_);
lean_closure_set(v___f_2361_, 10, v_inst_2328_);
lean_closure_set(v___f_2361_, 11, v_pre_2329_);
lean_closure_set(v___f_2361_, 12, v_post_2330_);
lean_closure_set(v___f_2361_, 13, v___x_2358_);
lean_closure_set(v___f_2361_, 14, v___x_2359_);
lean_closure_set(v___f_2361_, 15, v___x_2360_);
lean_closure_set(v___f_2361_, 16, v_postApp_2334_);
lean_closure_set(v___f_2361_, 17, v_x_2335_);
lean_closure_set(v___f_2361_, 18, v_x_2336_);
lean_closure_set(v___f_2361_, 19, v_toBind_2352_);
v___x_2362_ = lean_expr_instantiate_rev(v_type_2348_, v_fvars_2337_);
lean_dec_ref(v_fvars_2337_);
lean_dec_ref(v_type_2348_);
v___x_2363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2326_, v_inst_2327_, v_inst_2328_, v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v_postApp_2334_, v_x_2335_, v_x_2336_, v___x_2362_, v_a_2339_);
v___x_2364_ = lean_apply_4(v_toBind_2352_, lean_box(0), lean_box(0), v___x_2363_, v___f_2361_);
return v___x_2364_;
}
else
{
lean_object* v_toBind_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref_known(v___x_2346_, 2);
lean_dec_ref(v___x_2342_);
v_toBind_2365_ = lean_ctor_get(v_inst_2326_, 1);
lean_inc_n(v_toBind_2365_, 2);
v___x_2366_ = lean_box(v_usedLetOnly_2331_);
v___x_2367_ = lean_box(v_skipConstInApp_2332_);
v___x_2368_ = lean_box(v_skipInstances_2333_);
lean_inc(v_a_2339_);
lean_inc(v_x_2336_);
lean_inc(v_postApp_2334_);
lean_inc(v_post_2330_);
lean_inc(v_pre_2329_);
lean_inc_ref(v_inst_2328_);
lean_inc_n(v_inst_2327_, 2);
lean_inc_ref(v_inst_2326_);
v___f_2369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2369_, 0, v_inst_2326_);
lean_closure_set(v___f_2369_, 1, v_inst_2327_);
lean_closure_set(v___f_2369_, 2, v_inst_2328_);
lean_closure_set(v___f_2369_, 3, v_pre_2329_);
lean_closure_set(v___f_2369_, 4, v_post_2330_);
lean_closure_set(v___f_2369_, 5, v___x_2366_);
lean_closure_set(v___f_2369_, 6, v___x_2367_);
lean_closure_set(v___f_2369_, 7, v___x_2368_);
lean_closure_set(v___f_2369_, 8, v_postApp_2334_);
lean_closure_set(v___f_2369_, 9, v_x_2335_);
lean_closure_set(v___f_2369_, 10, v_x_2336_);
lean_closure_set(v___f_2369_, 11, v_a_2339_);
v___x_2370_ = lean_box(v_usedLetOnly_2331_);
lean_inc_ref(v_fvars_2337_);
v___f_2371_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2371_, 0, v_fvars_2337_);
lean_closure_set(v___f_2371_, 1, v___x_2370_);
lean_closure_set(v___f_2371_, 2, v_inst_2327_);
lean_closure_set(v___f_2371_, 3, v_toBind_2365_);
lean_closure_set(v___f_2371_, 4, v___f_2369_);
v___x_2372_ = lean_expr_instantiate_rev(v_e_2338_, v_fvars_2337_);
lean_dec_ref(v_fvars_2337_);
lean_dec_ref(v_e_2338_);
v___x_2373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2326_, v_inst_2327_, v_inst_2328_, v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v_postApp_2334_, v_x_2335_, v_x_2336_, v___x_2372_, v_a_2339_);
v___x_2374_ = lean_apply_4(v_toBind_2365_, lean_box(0), lean_box(0), v___x_2373_, v___f_2371_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_pre_2378_, lean_object* v_post_2379_, lean_object* v_usedLetOnly_2380_, lean_object* v_skipConstInApp_2381_, lean_object* v_skipInstances_2382_, lean_object* v_postApp_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_, lean_object* v___y_2386_, lean_object* v_a_2387_){
_start:
{
uint8_t v_usedLetOnly_boxed_2388_; uint8_t v_skipConstInApp_boxed_2389_; uint8_t v_skipInstances_boxed_2390_; lean_object* v_res_2391_; 
v_usedLetOnly_boxed_2388_ = lean_unbox(v_usedLetOnly_2380_);
v_skipConstInApp_boxed_2389_ = lean_unbox(v_skipConstInApp_2381_);
v_skipInstances_boxed_2390_ = lean_unbox(v_skipInstances_2382_);
v_res_2391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_inst_2375_, v_inst_2376_, v_inst_2377_, v_pre_2378_, v_post_2379_, v_usedLetOnly_boxed_2388_, v_skipConstInApp_boxed_2389_, v_skipInstances_boxed_2390_, v_postApp_2383_, v_x_2384_, v_x_2385_, v___y_2386_, v_a_2387_);
lean_dec(v___y_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_inst_2394_, lean_object* v_pre_2395_, lean_object* v_post_2396_, lean_object* v_usedLetOnly_2397_, lean_object* v_skipConstInApp_2398_, lean_object* v_skipInstances_2399_, lean_object* v_postApp_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_e_2403_, lean_object* v_a_2404_){
_start:
{
uint8_t v_usedLetOnly_boxed_2405_; uint8_t v_skipConstInApp_boxed_2406_; uint8_t v_skipInstances_boxed_2407_; lean_object* v_res_2408_; 
v_usedLetOnly_boxed_2405_ = lean_unbox(v_usedLetOnly_2397_);
v_skipConstInApp_boxed_2406_ = lean_unbox(v_skipConstInApp_2398_);
v_skipInstances_boxed_2407_ = lean_unbox(v_skipInstances_2399_);
v_res_2408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2392_, v_inst_2393_, v_inst_2394_, v_pre_2395_, v_post_2396_, v_usedLetOnly_boxed_2405_, v_skipConstInApp_boxed_2406_, v_skipInstances_boxed_2407_, v_postApp_2400_, v_x_2401_, v_x_2402_, v_e_2403_, v_a_2404_);
lean_dec(v_a_2404_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(lean_object* v___x_2409_, lean_object* v_toApplicative_2410_, lean_object* v_toBind_2411_, lean_object* v___f_2412_, lean_object* v_paramInfo_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_pre_2417_, lean_object* v_post_2418_, uint8_t v_usedLetOnly_2419_, uint8_t v_skipConstInApp_2420_, uint8_t v_skipInstances_2421_, lean_object* v_postApp_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_next_2425_, lean_object* v_acc_2426_, lean_object* v_h_2427_, lean_object* v_G_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_lt(v_next_2425_, v___x_2409_);
if (v___x_2430_ == 0)
{
lean_object* v_toPure_2431_; lean_object* v___x_2432_; 
lean_dec(v_G_2428_);
lean_dec(v_next_2425_);
lean_dec(v_x_2424_);
lean_dec(v_postApp_2422_);
lean_dec(v_post_2418_);
lean_dec(v_pre_2417_);
lean_dec_ref(v_inst_2416_);
lean_dec(v_inst_2415_);
lean_dec_ref(v_inst_2414_);
lean_dec(v___f_2412_);
lean_dec(v_toBind_2411_);
v_toPure_2431_ = lean_ctor_get(v_toApplicative_2410_, 1);
lean_inc(v_toPure_2431_);
lean_dec_ref(v_toApplicative_2410_);
v___x_2432_ = lean_apply_2(v_toPure_2431_, lean_box(0), v_acc_2426_);
return v___x_2432_;
}
else
{
lean_object* v___f_2433_; lean_object* v___y_2435_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
lean_inc(v___y_2429_);
lean_inc(v_next_2425_);
lean_inc_ref(v_toApplicative_2410_);
v___f_2433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_2433_, 0, v_toApplicative_2410_);
lean_closure_set(v___f_2433_, 1, v_next_2425_);
lean_closure_set(v___f_2433_, 2, v_G_2428_);
lean_closure_set(v___f_2433_, 3, v___y_2429_);
v___x_2438_ = lean_array_fget_borrowed(v_acc_2426_, v_next_2425_);
v___x_2439_ = lean_array_get_size(v_paramInfo_2413_);
v___x_2440_ = lean_nat_dec_lt(v_next_2425_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_inc(v___x_2438_);
v___f_2441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2441_, 0, v_toApplicative_2410_);
lean_closure_set(v___f_2441_, 1, v_acc_2426_);
lean_closure_set(v___f_2441_, 2, v_next_2425_);
v___x_2442_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_postApp_2422_, v_x_2423_, v_x_2424_, v___x_2438_, v___y_2429_);
lean_inc(v_toBind_2411_);
v___x_2443_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2442_, v___f_2441_);
v___y_2435_ = v___x_2443_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2444_; uint8_t v_isInstance_2445_; 
v___x_2444_ = lean_array_fget_borrowed(v_paramInfo_2413_, v_next_2425_);
v_isInstance_2445_ = lean_ctor_get_uint8(v___x_2444_, sizeof(void*)*1 + 4);
if (v_isInstance_2445_ == 0)
{
lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_inc(v___x_2438_);
v___f_2446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2446_, 0, v_toApplicative_2410_);
lean_closure_set(v___f_2446_, 1, v_acc_2426_);
lean_closure_set(v___f_2446_, 2, v_next_2425_);
v___x_2447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_postApp_2422_, v_x_2423_, v_x_2424_, v___x_2438_, v___y_2429_);
lean_inc(v_toBind_2411_);
v___x_2448_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2447_, v___f_2446_);
v___y_2435_ = v___x_2448_;
goto v___jp_2434_;
}
else
{
lean_object* v_toPure_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec(v_next_2425_);
lean_dec(v_x_2424_);
lean_dec(v_postApp_2422_);
lean_dec(v_post_2418_);
lean_dec(v_pre_2417_);
lean_dec_ref(v_inst_2416_);
lean_dec(v_inst_2415_);
lean_dec_ref(v_inst_2414_);
v_toPure_2449_ = lean_ctor_get(v_toApplicative_2410_, 1);
lean_inc(v_toPure_2449_);
lean_dec_ref(v_toApplicative_2410_);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_acc_2426_);
v___x_2451_ = lean_apply_2(v_toPure_2449_, lean_box(0), v___x_2450_);
v___y_2435_ = v___x_2451_;
goto v___jp_2434_;
}
}
v___jp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_inc(v_toBind_2411_);
v___x_2436_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___y_2435_, v___f_2412_);
v___x_2437_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2436_, v___f_2433_);
return v___x_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_2452_ = _args[0];
lean_object* v_toApplicative_2453_ = _args[1];
lean_object* v_toBind_2454_ = _args[2];
lean_object* v___f_2455_ = _args[3];
lean_object* v_paramInfo_2456_ = _args[4];
lean_object* v_inst_2457_ = _args[5];
lean_object* v_inst_2458_ = _args[6];
lean_object* v_inst_2459_ = _args[7];
lean_object* v_pre_2460_ = _args[8];
lean_object* v_post_2461_ = _args[9];
lean_object* v_usedLetOnly_2462_ = _args[10];
lean_object* v_skipConstInApp_2463_ = _args[11];
lean_object* v_skipInstances_2464_ = _args[12];
lean_object* v_postApp_2465_ = _args[13];
lean_object* v_x_2466_ = _args[14];
lean_object* v_x_2467_ = _args[15];
lean_object* v_next_2468_ = _args[16];
lean_object* v_acc_2469_ = _args[17];
lean_object* v_h_2470_ = _args[18];
lean_object* v_G_2471_ = _args[19];
lean_object* v___y_2472_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_2473_; uint8_t v_skipConstInApp_boxed_2474_; uint8_t v_skipInstances_boxed_2475_; lean_object* v_res_2476_; 
v_usedLetOnly_boxed_2473_ = lean_unbox(v_usedLetOnly_2462_);
v_skipConstInApp_boxed_2474_ = lean_unbox(v_skipConstInApp_2463_);
v_skipInstances_boxed_2475_ = lean_unbox(v_skipInstances_2464_);
v_res_2476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v___x_2452_, v_toApplicative_2453_, v_toBind_2454_, v___f_2455_, v_paramInfo_2456_, v_inst_2457_, v_inst_2458_, v_inst_2459_, v_pre_2460_, v_post_2461_, v_usedLetOnly_boxed_2473_, v_skipConstInApp_boxed_2474_, v_skipInstances_boxed_2475_, v_postApp_2465_, v_x_2466_, v_x_2467_, v_next_2468_, v_acc_2469_, v_h_2470_, v_G_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v_paramInfo_2456_);
lean_dec(v___x_2452_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2477_, lean_object* v_toApplicative_2478_, lean_object* v_toBind_2479_, lean_object* v___f_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_pre_2484_, lean_object* v_post_2485_, uint8_t v_usedLetOnly_2486_, uint8_t v_skipConstInApp_2487_, uint8_t v_skipInstances_2488_, lean_object* v_postApp_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_, lean_object* v_args_2492_, lean_object* v___y_2493_, lean_object* v___f_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_paramInfo_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___f_2501_; lean_object* v___x_3272__overap_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_paramInfo_2496_ = lean_ctor_get(v_a_2495_, 0);
lean_inc_ref(v_paramInfo_2496_);
lean_dec_ref(v_a_2495_);
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = lean_box(v_usedLetOnly_2486_);
v___x_2499_ = lean_box(v_skipConstInApp_2487_);
v___x_2500_ = lean_box(v_skipInstances_2488_);
lean_inc(v_toBind_2479_);
v___f_2501_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 21, 16);
lean_closure_set(v___f_2501_, 0, v___x_2477_);
lean_closure_set(v___f_2501_, 1, v_toApplicative_2478_);
lean_closure_set(v___f_2501_, 2, v_toBind_2479_);
lean_closure_set(v___f_2501_, 3, v___f_2480_);
lean_closure_set(v___f_2501_, 4, v_paramInfo_2496_);
lean_closure_set(v___f_2501_, 5, v_inst_2481_);
lean_closure_set(v___f_2501_, 6, v_inst_2482_);
lean_closure_set(v___f_2501_, 7, v_inst_2483_);
lean_closure_set(v___f_2501_, 8, v_pre_2484_);
lean_closure_set(v___f_2501_, 9, v_post_2485_);
lean_closure_set(v___f_2501_, 10, v___x_2498_);
lean_closure_set(v___f_2501_, 11, v___x_2499_);
lean_closure_set(v___f_2501_, 12, v___x_2500_);
lean_closure_set(v___f_2501_, 13, v_postApp_2489_);
lean_closure_set(v___f_2501_, 14, v_x_2490_);
lean_closure_set(v___f_2501_, 15, v_x_2491_);
v___x_3272__overap_2502_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2501_, v___x_2497_, v_args_2492_, lean_box(0));
lean_inc(v___y_2493_);
v___x_2503_ = lean_apply_1(v___x_3272__overap_2502_, v___y_2493_);
v___x_2504_ = lean_apply_4(v_toBind_2479_, lean_box(0), lean_box(0), v___x_2503_, v___f_2494_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2505_ = _args[0];
lean_object* v_toApplicative_2506_ = _args[1];
lean_object* v_toBind_2507_ = _args[2];
lean_object* v___f_2508_ = _args[3];
lean_object* v_inst_2509_ = _args[4];
lean_object* v_inst_2510_ = _args[5];
lean_object* v_inst_2511_ = _args[6];
lean_object* v_pre_2512_ = _args[7];
lean_object* v_post_2513_ = _args[8];
lean_object* v_usedLetOnly_2514_ = _args[9];
lean_object* v_skipConstInApp_2515_ = _args[10];
lean_object* v_skipInstances_2516_ = _args[11];
lean_object* v_postApp_2517_ = _args[12];
lean_object* v_x_2518_ = _args[13];
lean_object* v_x_2519_ = _args[14];
lean_object* v_args_2520_ = _args[15];
lean_object* v___y_2521_ = _args[16];
lean_object* v___f_2522_ = _args[17];
lean_object* v_a_2523_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_2524_; uint8_t v_skipConstInApp_boxed_2525_; uint8_t v_skipInstances_boxed_2526_; lean_object* v_res_2527_; 
v_usedLetOnly_boxed_2524_ = lean_unbox(v_usedLetOnly_2514_);
v_skipConstInApp_boxed_2525_ = lean_unbox(v_skipConstInApp_2515_);
v_skipInstances_boxed_2526_ = lean_unbox(v_skipInstances_2516_);
v_res_2527_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2505_, v_toApplicative_2506_, v_toBind_2507_, v___f_2508_, v_inst_2509_, v_inst_2510_, v_inst_2511_, v_pre_2512_, v_post_2513_, v_usedLetOnly_boxed_2524_, v_skipConstInApp_boxed_2525_, v_skipInstances_boxed_2526_, v_postApp_2517_, v_x_2518_, v_x_2519_, v_args_2520_, v___y_2521_, v___f_2522_, v_a_2523_);
lean_dec(v___y_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(uint8_t v_skipInstances_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_pre_2532_, lean_object* v_post_2533_, uint8_t v_usedLetOnly_2534_, uint8_t v_skipConstInApp_2535_, lean_object* v_postApp_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_, lean_object* v___y_2539_, lean_object* v_toBind_2540_, lean_object* v_args_2541_, lean_object* v___x_2542_, lean_object* v_toApplicative_2543_, lean_object* v___f_2544_, lean_object* v_f_2545_, lean_object* v___y_2546_){
_start:
{
if (v_skipInstances_2528_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; size_t v_sz_2556_; size_t v___x_2557_; lean_object* v___x_3287__overap_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v___f_2544_);
lean_dec_ref(v_toApplicative_2543_);
v___x_2547_ = lean_box(v_usedLetOnly_2534_);
v___x_2548_ = lean_box(v_skipConstInApp_2535_);
v___x_2549_ = lean_box(v_skipInstances_2528_);
lean_inc_n(v___y_2546_, 2);
lean_inc(v_x_2538_);
lean_inc_n(v_postApp_2536_, 2);
lean_inc(v_post_2533_);
lean_inc(v_pre_2532_);
lean_inc_ref(v_inst_2531_);
lean_inc(v_inst_2530_);
lean_inc_ref(v_inst_2529_);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2550_, 0, v_inst_2529_);
lean_closure_set(v___f_2550_, 1, v_inst_2530_);
lean_closure_set(v___f_2550_, 2, v_inst_2531_);
lean_closure_set(v___f_2550_, 3, v_pre_2532_);
lean_closure_set(v___f_2550_, 4, v_post_2533_);
lean_closure_set(v___f_2550_, 5, v___x_2547_);
lean_closure_set(v___f_2550_, 6, v___x_2548_);
lean_closure_set(v___f_2550_, 7, v___x_2549_);
lean_closure_set(v___f_2550_, 8, v_postApp_2536_);
lean_closure_set(v___f_2550_, 9, v_x_2537_);
lean_closure_set(v___f_2550_, 10, v_x_2538_);
lean_closure_set(v___f_2550_, 11, v___y_2546_);
lean_inc(v_toBind_2540_);
v___f_2551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2551_, 0, v_f_2545_);
lean_closure_set(v___f_2551_, 1, v_postApp_2536_);
lean_closure_set(v___f_2551_, 2, v___y_2539_);
lean_closure_set(v___f_2551_, 3, v_toBind_2540_);
lean_closure_set(v___f_2551_, 4, v___f_2550_);
v___x_2552_ = lean_box(v_usedLetOnly_2534_);
v___x_2553_ = lean_box(v_skipConstInApp_2535_);
v___x_2554_ = lean_box(v_skipInstances_2528_);
v___x_2555_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 13, 11);
lean_closure_set(v___x_2555_, 0, v_inst_2529_);
lean_closure_set(v___x_2555_, 1, v_inst_2530_);
lean_closure_set(v___x_2555_, 2, v_inst_2531_);
lean_closure_set(v___x_2555_, 3, v_pre_2532_);
lean_closure_set(v___x_2555_, 4, v_post_2533_);
lean_closure_set(v___x_2555_, 5, v___x_2552_);
lean_closure_set(v___x_2555_, 6, v___x_2553_);
lean_closure_set(v___x_2555_, 7, v___x_2554_);
lean_closure_set(v___x_2555_, 8, v_postApp_2536_);
lean_closure_set(v___x_2555_, 9, v_x_2537_);
lean_closure_set(v___x_2555_, 10, v_x_2538_);
v_sz_2556_ = lean_array_size(v_args_2541_);
v___x_2557_ = ((size_t)0ULL);
v___x_3287__overap_2558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2542_, v___x_2555_, v_sz_2556_, v___x_2557_, v_args_2541_);
v___x_2559_ = lean_apply_1(v___x_3287__overap_2558_, v___y_2546_);
v___x_2560_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2559_, v___f_2551_);
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref(v___x_2542_);
v___x_2561_ = lean_box(v_usedLetOnly_2534_);
v___x_2562_ = lean_box(v_skipConstInApp_2535_);
v___x_2563_ = lean_box(v_skipInstances_2528_);
lean_inc_n(v___y_2546_, 2);
lean_inc(v_x_2538_);
lean_inc_n(v_postApp_2536_, 2);
lean_inc(v_post_2533_);
lean_inc(v_pre_2532_);
lean_inc_ref(v_inst_2531_);
lean_inc_n(v_inst_2530_, 2);
lean_inc_ref(v_inst_2529_);
v___f_2564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2564_, 0, v_inst_2529_);
lean_closure_set(v___f_2564_, 1, v_inst_2530_);
lean_closure_set(v___f_2564_, 2, v_inst_2531_);
lean_closure_set(v___f_2564_, 3, v_pre_2532_);
lean_closure_set(v___f_2564_, 4, v_post_2533_);
lean_closure_set(v___f_2564_, 5, v___x_2561_);
lean_closure_set(v___f_2564_, 6, v___x_2562_);
lean_closure_set(v___f_2564_, 7, v___x_2563_);
lean_closure_set(v___f_2564_, 8, v_postApp_2536_);
lean_closure_set(v___f_2564_, 9, v_x_2537_);
lean_closure_set(v___f_2564_, 10, v_x_2538_);
lean_closure_set(v___f_2564_, 11, v___y_2546_);
lean_inc_n(v_toBind_2540_, 2);
lean_inc_ref(v_f_2545_);
v___f_2565_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2565_, 0, v_f_2545_);
lean_closure_set(v___f_2565_, 1, v_postApp_2536_);
lean_closure_set(v___f_2565_, 2, v___y_2539_);
lean_closure_set(v___f_2565_, 3, v_toBind_2540_);
lean_closure_set(v___f_2565_, 4, v___f_2564_);
v___x_2566_ = lean_array_get_size(v_args_2541_);
v___x_2567_ = lean_box(v_usedLetOnly_2534_);
v___x_2568_ = lean_box(v_skipConstInApp_2535_);
v___x_2569_ = lean_box(v_skipInstances_2528_);
v___f_2570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 19, 18);
lean_closure_set(v___f_2570_, 0, v___x_2566_);
lean_closure_set(v___f_2570_, 1, v_toApplicative_2543_);
lean_closure_set(v___f_2570_, 2, v_toBind_2540_);
lean_closure_set(v___f_2570_, 3, v___f_2544_);
lean_closure_set(v___f_2570_, 4, v_inst_2529_);
lean_closure_set(v___f_2570_, 5, v_inst_2530_);
lean_closure_set(v___f_2570_, 6, v_inst_2531_);
lean_closure_set(v___f_2570_, 7, v_pre_2532_);
lean_closure_set(v___f_2570_, 8, v_post_2533_);
lean_closure_set(v___f_2570_, 9, v___x_2567_);
lean_closure_set(v___f_2570_, 10, v___x_2568_);
lean_closure_set(v___f_2570_, 11, v___x_2569_);
lean_closure_set(v___f_2570_, 12, v_postApp_2536_);
lean_closure_set(v___f_2570_, 13, v_x_2537_);
lean_closure_set(v___f_2570_, 14, v_x_2538_);
lean_closure_set(v___f_2570_, 15, v_args_2541_);
lean_closure_set(v___f_2570_, 16, v___y_2546_);
lean_closure_set(v___f_2570_, 17, v___f_2565_);
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2571_, 0, v_f_2545_);
lean_closure_set(v___x_2571_, 1, v___x_2566_);
v___x_2572_ = lean_apply_2(v_inst_2530_, lean_box(0), v___x_2571_);
v___x_2573_ = lean_apply_4(v_toBind_2540_, lean_box(0), lean_box(0), v___x_2572_, v___f_2570_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_skipInstances_2574_ = _args[0];
lean_object* v_inst_2575_ = _args[1];
lean_object* v_inst_2576_ = _args[2];
lean_object* v_inst_2577_ = _args[3];
lean_object* v_pre_2578_ = _args[4];
lean_object* v_post_2579_ = _args[5];
lean_object* v_usedLetOnly_2580_ = _args[6];
lean_object* v_skipConstInApp_2581_ = _args[7];
lean_object* v_postApp_2582_ = _args[8];
lean_object* v_x_2583_ = _args[9];
lean_object* v_x_2584_ = _args[10];
lean_object* v___y_2585_ = _args[11];
lean_object* v_toBind_2586_ = _args[12];
lean_object* v_args_2587_ = _args[13];
lean_object* v___x_2588_ = _args[14];
lean_object* v_toApplicative_2589_ = _args[15];
lean_object* v___f_2590_ = _args[16];
lean_object* v_f_2591_ = _args[17];
lean_object* v___y_2592_ = _args[18];
_start:
{
uint8_t v_skipInstances_boxed_2593_; uint8_t v_usedLetOnly_boxed_2594_; uint8_t v_skipConstInApp_boxed_2595_; lean_object* v_res_2596_; 
v_skipInstances_boxed_2593_ = lean_unbox(v_skipInstances_2574_);
v_usedLetOnly_boxed_2594_ = lean_unbox(v_usedLetOnly_2580_);
v_skipConstInApp_boxed_2595_ = lean_unbox(v_skipConstInApp_2581_);
v_res_2596_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v_skipInstances_boxed_2593_, v_inst_2575_, v_inst_2576_, v_inst_2577_, v_pre_2578_, v_post_2579_, v_usedLetOnly_boxed_2594_, v_skipConstInApp_boxed_2595_, v_postApp_2582_, v_x_2583_, v_x_2584_, v___y_2585_, v_toBind_2586_, v_args_2587_, v___x_2588_, v_toApplicative_2589_, v___f_2590_, v_f_2591_, v___y_2592_);
lean_dec(v___y_2592_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(uint8_t v_skipInstances_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_pre_2601_, lean_object* v_post_2602_, uint8_t v_usedLetOnly_2603_, uint8_t v_skipConstInApp_2604_, lean_object* v_postApp_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v_toBind_2609_, lean_object* v___x_2610_, lean_object* v_toApplicative_2611_, lean_object* v___f_2612_, lean_object* v_f_2613_, lean_object* v_args_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; 
v___x_2616_ = lean_box(v_skipInstances_2597_);
v___x_2617_ = lean_box(v_usedLetOnly_2603_);
v___x_2618_ = lean_box(v_skipConstInApp_2604_);
lean_inc_ref(v_toApplicative_2611_);
lean_inc(v_toBind_2609_);
lean_inc(v_x_2607_);
lean_inc(v_postApp_2605_);
lean_inc(v_post_2602_);
lean_inc(v_pre_2601_);
lean_inc_ref(v_inst_2600_);
lean_inc(v_inst_2599_);
lean_inc_ref(v_inst_2598_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 19, 17);
lean_closure_set(v___f_2619_, 0, v___x_2616_);
lean_closure_set(v___f_2619_, 1, v_inst_2598_);
lean_closure_set(v___f_2619_, 2, v_inst_2599_);
lean_closure_set(v___f_2619_, 3, v_inst_2600_);
lean_closure_set(v___f_2619_, 4, v_pre_2601_);
lean_closure_set(v___f_2619_, 5, v_post_2602_);
lean_closure_set(v___f_2619_, 6, v___x_2617_);
lean_closure_set(v___f_2619_, 7, v___x_2618_);
lean_closure_set(v___f_2619_, 8, v_postApp_2605_);
lean_closure_set(v___f_2619_, 9, v_x_2606_);
lean_closure_set(v___f_2619_, 10, v_x_2607_);
lean_closure_set(v___f_2619_, 11, v___y_2608_);
lean_closure_set(v___f_2619_, 12, v_toBind_2609_);
lean_closure_set(v___f_2619_, 13, v_args_2614_);
lean_closure_set(v___f_2619_, 14, v___x_2610_);
lean_closure_set(v___f_2619_, 15, v_toApplicative_2611_);
lean_closure_set(v___f_2619_, 16, v___f_2612_);
lean_inc(v___y_2615_);
v___f_2620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2620_, 0, v___f_2619_);
lean_closure_set(v___f_2620_, 1, v___y_2615_);
if (v_skipConstInApp_2604_ == 0)
{
lean_dec_ref(v_toApplicative_2611_);
goto v___jp_2621_;
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Expr_isConst(v_f_2613_);
if (v___x_2624_ == 0)
{
lean_dec_ref(v_toApplicative_2611_);
goto v___jp_2621_;
}
else
{
lean_object* v_toPure_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v_x_2607_);
lean_dec(v_postApp_2605_);
lean_dec(v_post_2602_);
lean_dec(v_pre_2601_);
lean_dec_ref(v_inst_2600_);
lean_dec(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
v_toPure_2625_ = lean_ctor_get(v_toApplicative_2611_, 1);
lean_inc(v_toPure_2625_);
lean_dec_ref(v_toApplicative_2611_);
v___x_2626_ = lean_apply_2(v_toPure_2625_, lean_box(0), v_f_2613_);
v___x_2627_ = lean_apply_4(v_toBind_2609_, lean_box(0), lean_box(0), v___x_2626_, v___f_2620_);
return v___x_2627_;
}
}
v___jp_2621_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2598_, v_inst_2599_, v_inst_2600_, v_pre_2601_, v_post_2602_, v_usedLetOnly_2603_, v_skipConstInApp_2604_, v_skipInstances_2597_, v_postApp_2605_, v_x_2606_, v_x_2607_, v_f_2613_, v___y_2615_);
v___x_2623_ = lean_apply_4(v_toBind_2609_, lean_box(0), lean_box(0), v___x_2622_, v___f_2620_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_skipInstances_2628_ = _args[0];
lean_object* v_inst_2629_ = _args[1];
lean_object* v_inst_2630_ = _args[2];
lean_object* v_inst_2631_ = _args[3];
lean_object* v_pre_2632_ = _args[4];
lean_object* v_post_2633_ = _args[5];
lean_object* v_usedLetOnly_2634_ = _args[6];
lean_object* v_skipConstInApp_2635_ = _args[7];
lean_object* v_postApp_2636_ = _args[8];
lean_object* v_x_2637_ = _args[9];
lean_object* v_x_2638_ = _args[10];
lean_object* v___y_2639_ = _args[11];
lean_object* v_toBind_2640_ = _args[12];
lean_object* v___x_2641_ = _args[13];
lean_object* v_toApplicative_2642_ = _args[14];
lean_object* v___f_2643_ = _args[15];
lean_object* v_f_2644_ = _args[16];
lean_object* v_args_2645_ = _args[17];
lean_object* v___y_2646_ = _args[18];
_start:
{
uint8_t v_skipInstances_boxed_2647_; uint8_t v_usedLetOnly_boxed_2648_; uint8_t v_skipConstInApp_boxed_2649_; lean_object* v_res_2650_; 
v_skipInstances_boxed_2647_ = lean_unbox(v_skipInstances_2628_);
v_usedLetOnly_boxed_2648_ = lean_unbox(v_usedLetOnly_2634_);
v_skipConstInApp_boxed_2649_ = lean_unbox(v_skipConstInApp_2635_);
v_res_2650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_skipInstances_boxed_2647_, v_inst_2629_, v_inst_2630_, v_inst_2631_, v_pre_2632_, v_post_2633_, v_usedLetOnly_boxed_2648_, v_skipConstInApp_boxed_2649_, v_postApp_2636_, v_x_2637_, v_x_2638_, v___y_2639_, v_toBind_2640_, v___x_2641_, v_toApplicative_2642_, v___f_2643_, v_f_2644_, v_args_2645_, v___y_2646_);
lean_dec(v___y_2646_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(lean_object* v_expr_2651_, lean_object* v_data_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_pre_2656_, lean_object* v_post_2657_, uint8_t v_usedLetOnly_2658_, uint8_t v_skipConstInApp_2659_, uint8_t v_skipInstances_2660_, lean_object* v_postApp_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v_a_2666_){
_start:
{
size_t v___x_2667_; size_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = lean_ptr_addr(v_expr_2651_);
v___x_2668_ = lean_ptr_addr(v_a_2666_);
v___x_2669_ = lean_usize_dec_eq(v___x_2667_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v___y_2665_);
v___x_2670_ = l_Lean_Expr_mdata___override(v_data_2652_, v_a_2666_);
v___x_2671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2653_, v_inst_2654_, v_inst_2655_, v_pre_2656_, v_post_2657_, v_usedLetOnly_2658_, v_skipConstInApp_2659_, v_skipInstances_2660_, v_postApp_2661_, v_x_2662_, v_x_2663_, v___x_2670_, v___y_2664_);
return v___x_2671_;
}
else
{
lean_object* v___x_2672_; 
lean_dec_ref(v_a_2666_);
lean_dec(v_data_2652_);
v___x_2672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2653_, v_inst_2654_, v_inst_2655_, v_pre_2656_, v_post_2657_, v_usedLetOnly_2658_, v_skipConstInApp_2659_, v_skipInstances_2660_, v_postApp_2661_, v_x_2662_, v_x_2663_, v___y_2665_, v___y_2664_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object* v_expr_2673_, lean_object* v_data_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_pre_2678_, lean_object* v_post_2679_, lean_object* v_usedLetOnly_2680_, lean_object* v_skipConstInApp_2681_, lean_object* v_skipInstances_2682_, lean_object* v_postApp_2683_, lean_object* v_x_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v_a_2688_){
_start:
{
uint8_t v_usedLetOnly_boxed_2689_; uint8_t v_skipConstInApp_boxed_2690_; uint8_t v_skipInstances_boxed_2691_; lean_object* v_res_2692_; 
v_usedLetOnly_boxed_2689_ = lean_unbox(v_usedLetOnly_2680_);
v_skipConstInApp_boxed_2690_ = lean_unbox(v_skipConstInApp_2681_);
v_skipInstances_boxed_2691_ = lean_unbox(v_skipInstances_2682_);
v_res_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_expr_2673_, v_data_2674_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_pre_2678_, v_post_2679_, v_usedLetOnly_boxed_2689_, v_skipConstInApp_boxed_2690_, v_skipInstances_boxed_2691_, v_postApp_2683_, v_x_2684_, v_x_2685_, v___y_2686_, v___y_2687_, v_a_2688_);
lean_dec(v___y_2686_);
lean_dec_ref(v_expr_2673_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_struct_2693_, lean_object* v_typeName_2694_, lean_object* v_idx_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_pre_2699_, lean_object* v_post_2700_, uint8_t v_usedLetOnly_2701_, uint8_t v_skipConstInApp_2702_, uint8_t v_skipInstances_2703_, lean_object* v_postApp_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v_a_2709_){
_start:
{
size_t v___x_2710_; size_t v___x_2711_; uint8_t v___x_2712_; 
v___x_2710_ = lean_ptr_addr(v_struct_2693_);
v___x_2711_ = lean_ptr_addr(v_a_2709_);
v___x_2712_ = lean_usize_dec_eq(v___x_2710_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v___y_2708_);
v___x_2713_ = l_Lean_Expr_proj___override(v_typeName_2694_, v_idx_2695_, v_a_2709_);
v___x_2714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2696_, v_inst_2697_, v_inst_2698_, v_pre_2699_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v_postApp_2704_, v_x_2705_, v_x_2706_, v___x_2713_, v___y_2707_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; 
lean_dec_ref(v_a_2709_);
lean_dec(v_idx_2695_);
lean_dec(v_typeName_2694_);
v___x_2715_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2696_, v_inst_2697_, v_inst_2698_, v_pre_2699_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v_postApp_2704_, v_x_2705_, v_x_2706_, v___y_2708_, v___y_2707_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_struct_2716_ = _args[0];
lean_object* v_typeName_2717_ = _args[1];
lean_object* v_idx_2718_ = _args[2];
lean_object* v_inst_2719_ = _args[3];
lean_object* v_inst_2720_ = _args[4];
lean_object* v_inst_2721_ = _args[5];
lean_object* v_pre_2722_ = _args[6];
lean_object* v_post_2723_ = _args[7];
lean_object* v_usedLetOnly_2724_ = _args[8];
lean_object* v_skipConstInApp_2725_ = _args[9];
lean_object* v_skipInstances_2726_ = _args[10];
lean_object* v_postApp_2727_ = _args[11];
lean_object* v_x_2728_ = _args[12];
lean_object* v_x_2729_ = _args[13];
lean_object* v___y_2730_ = _args[14];
lean_object* v___y_2731_ = _args[15];
lean_object* v_a_2732_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2733_; uint8_t v_skipConstInApp_boxed_2734_; uint8_t v_skipInstances_boxed_2735_; lean_object* v_res_2736_; 
v_usedLetOnly_boxed_2733_ = lean_unbox(v_usedLetOnly_2724_);
v_skipConstInApp_boxed_2734_ = lean_unbox(v_skipConstInApp_2725_);
v_skipInstances_boxed_2735_ = lean_unbox(v_skipInstances_2726_);
v_res_2736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_struct_2716_, v_typeName_2717_, v_idx_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_pre_2722_, v_post_2723_, v_usedLetOnly_boxed_2733_, v_skipConstInApp_boxed_2734_, v_skipInstances_boxed_2735_, v_postApp_2727_, v_x_2728_, v_x_2729_, v___y_2730_, v___y_2731_, v_a_2732_);
lean_dec(v___y_2730_);
lean_dec_ref(v_struct_2716_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_pre_2741_, lean_object* v_post_2742_, uint8_t v_usedLetOnly_2743_, uint8_t v_skipConstInApp_2744_, uint8_t v_skipInstances_2745_, lean_object* v_postApp_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v_toBind_2750_, lean_object* v___x_2751_, lean_object* v___f_2752_, lean_object* v_e_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___y_2756_; 
switch(lean_obj_tag(v_a_2754_))
{
case 0:
{
lean_object* v_e_2792_; lean_object* v_toPure_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_e_2753_);
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec(v_x_2748_);
lean_dec(v_postApp_2746_);
lean_dec(v_post_2742_);
lean_dec(v_pre_2741_);
lean_dec_ref(v_inst_2740_);
lean_dec(v_inst_2739_);
lean_dec_ref(v_inst_2738_);
v_e_2792_ = lean_ctor_get(v_a_2754_, 0);
lean_inc_ref(v_e_2792_);
lean_dec_ref_known(v_a_2754_, 1);
v_toPure_2793_ = lean_ctor_get(v_toApplicative_2737_, 1);
lean_inc(v_toPure_2793_);
lean_dec_ref(v_toApplicative_2737_);
v___x_2794_ = lean_apply_2(v_toPure_2793_, lean_box(0), v_e_2792_);
return v___x_2794_;
}
case 1:
{
lean_object* v_e_2795_; lean_object* v___x_2796_; 
lean_dec_ref(v_e_2753_);
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec_ref(v_toApplicative_2737_);
v_e_2795_ = lean_ctor_get(v_a_2754_, 0);
lean_inc_ref(v_e_2795_);
lean_dec_ref_known(v_a_2754_, 1);
v___x_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v_e_2795_, v___y_2749_);
return v___x_2796_;
}
default: 
{
lean_object* v_e_x3f_2797_; 
v_e_x3f_2797_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_e_x3f_2797_);
lean_dec_ref_known(v_a_2754_, 1);
if (lean_obj_tag(v_e_x3f_2797_) == 0)
{
v___y_2756_ = v_e_2753_;
goto v___jp_2755_;
}
else
{
lean_object* v_val_2798_; 
lean_dec_ref(v_e_2753_);
v_val_2798_ = lean_ctor_get(v_e_x3f_2797_, 0);
lean_inc(v_val_2798_);
lean_dec_ref_known(v_e_x3f_2797_, 1);
v___y_2756_ = v_val_2798_;
goto v___jp_2755_;
}
}
}
v___jp_2755_:
{
switch(lean_obj_tag(v___y_2756_))
{
case 7:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec_ref(v_toApplicative_2737_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v___x_2757_, v___y_2756_, v___y_2749_);
return v___x_2758_;
}
case 6:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec_ref(v_toApplicative_2737_);
v___x_2759_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v___x_2759_, v___y_2756_, v___y_2749_);
return v___x_2760_;
}
case 8:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec_ref(v_toApplicative_2737_);
v___x_2761_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v___x_2761_, v___y_2756_, v___y_2749_);
return v___x_2762_;
}
case 5:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v_dummy_2767_; lean_object* v_nargs_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_3395__overap_2772_; lean_object* v___x_2773_; 
v___x_2763_ = lean_box(v_skipInstances_2745_);
v___x_2764_ = lean_box(v_usedLetOnly_2743_);
v___x_2765_ = lean_box(v_skipConstInApp_2744_);
lean_inc_ref(v___y_2756_);
v___f_2766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 19, 16);
lean_closure_set(v___f_2766_, 0, v___x_2763_);
lean_closure_set(v___f_2766_, 1, v_inst_2738_);
lean_closure_set(v___f_2766_, 2, v_inst_2739_);
lean_closure_set(v___f_2766_, 3, v_inst_2740_);
lean_closure_set(v___f_2766_, 4, v_pre_2741_);
lean_closure_set(v___f_2766_, 5, v_post_2742_);
lean_closure_set(v___f_2766_, 6, v___x_2764_);
lean_closure_set(v___f_2766_, 7, v___x_2765_);
lean_closure_set(v___f_2766_, 8, v_postApp_2746_);
lean_closure_set(v___f_2766_, 9, v_x_2747_);
lean_closure_set(v___f_2766_, 10, v_x_2748_);
lean_closure_set(v___f_2766_, 11, v___y_2756_);
lean_closure_set(v___f_2766_, 12, v_toBind_2750_);
lean_closure_set(v___f_2766_, 13, v___x_2751_);
lean_closure_set(v___f_2766_, 14, v_toApplicative_2737_);
lean_closure_set(v___f_2766_, 15, v___f_2752_);
v_dummy_2767_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_2768_ = l_Lean_Expr_getAppNumArgs(v___y_2756_);
lean_inc(v_nargs_2768_);
v___x_2769_ = lean_mk_array(v_nargs_2768_, v_dummy_2767_);
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_sub(v_nargs_2768_, v___x_2770_);
lean_dec(v_nargs_2768_);
v___x_3395__overap_2772_ = l_Lean_Expr_withAppAux___redArg(v___f_2766_, v___y_2756_, v___x_2769_, v___x_2771_);
lean_inc(v___y_2749_);
v___x_2773_ = lean_apply_1(v___x_3395__overap_2772_, v___y_2749_);
return v___x_2773_;
}
case 10:
{
lean_object* v_data_2774_; lean_object* v_expr_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec_ref(v_toApplicative_2737_);
v_data_2774_ = lean_ctor_get(v___y_2756_, 0);
lean_inc(v_data_2774_);
v_expr_2775_ = lean_ctor_get(v___y_2756_, 1);
lean_inc_ref_n(v_expr_2775_, 2);
v___x_2776_ = lean_box(v_usedLetOnly_2743_);
v___x_2777_ = lean_box(v_skipConstInApp_2744_);
v___x_2778_ = lean_box(v_skipInstances_2745_);
lean_inc(v___y_2749_);
lean_inc(v_x_2748_);
lean_inc(v_postApp_2746_);
lean_inc(v_post_2742_);
lean_inc(v_pre_2741_);
lean_inc_ref(v_inst_2740_);
lean_inc(v_inst_2739_);
lean_inc_ref(v_inst_2738_);
v___f_2779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 16, 15);
lean_closure_set(v___f_2779_, 0, v_expr_2775_);
lean_closure_set(v___f_2779_, 1, v_data_2774_);
lean_closure_set(v___f_2779_, 2, v_inst_2738_);
lean_closure_set(v___f_2779_, 3, v_inst_2739_);
lean_closure_set(v___f_2779_, 4, v_inst_2740_);
lean_closure_set(v___f_2779_, 5, v_pre_2741_);
lean_closure_set(v___f_2779_, 6, v_post_2742_);
lean_closure_set(v___f_2779_, 7, v___x_2776_);
lean_closure_set(v___f_2779_, 8, v___x_2777_);
lean_closure_set(v___f_2779_, 9, v___x_2778_);
lean_closure_set(v___f_2779_, 10, v_postApp_2746_);
lean_closure_set(v___f_2779_, 11, v_x_2747_);
lean_closure_set(v___f_2779_, 12, v_x_2748_);
lean_closure_set(v___f_2779_, 13, v___y_2749_);
lean_closure_set(v___f_2779_, 14, v___y_2756_);
v___x_2780_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v_expr_2775_, v___y_2749_);
v___x_2781_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2780_, v___f_2779_);
return v___x_2781_;
}
case 11:
{
lean_object* v_typeName_2782_; lean_object* v_idx_2783_; lean_object* v_struct_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___f_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec_ref(v_toApplicative_2737_);
v_typeName_2782_ = lean_ctor_get(v___y_2756_, 0);
lean_inc(v_typeName_2782_);
v_idx_2783_ = lean_ctor_get(v___y_2756_, 1);
lean_inc(v_idx_2783_);
v_struct_2784_ = lean_ctor_get(v___y_2756_, 2);
lean_inc_ref_n(v_struct_2784_, 2);
v___x_2785_ = lean_box(v_usedLetOnly_2743_);
v___x_2786_ = lean_box(v_skipConstInApp_2744_);
v___x_2787_ = lean_box(v_skipInstances_2745_);
lean_inc(v___y_2749_);
lean_inc(v_x_2748_);
lean_inc(v_postApp_2746_);
lean_inc(v_post_2742_);
lean_inc(v_pre_2741_);
lean_inc_ref(v_inst_2740_);
lean_inc(v_inst_2739_);
lean_inc_ref(v_inst_2738_);
v___f_2788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_2788_, 0, v_struct_2784_);
lean_closure_set(v___f_2788_, 1, v_typeName_2782_);
lean_closure_set(v___f_2788_, 2, v_idx_2783_);
lean_closure_set(v___f_2788_, 3, v_inst_2738_);
lean_closure_set(v___f_2788_, 4, v_inst_2739_);
lean_closure_set(v___f_2788_, 5, v_inst_2740_);
lean_closure_set(v___f_2788_, 6, v_pre_2741_);
lean_closure_set(v___f_2788_, 7, v_post_2742_);
lean_closure_set(v___f_2788_, 8, v___x_2785_);
lean_closure_set(v___f_2788_, 9, v___x_2786_);
lean_closure_set(v___f_2788_, 10, v___x_2787_);
lean_closure_set(v___f_2788_, 11, v_postApp_2746_);
lean_closure_set(v___f_2788_, 12, v_x_2747_);
lean_closure_set(v___f_2788_, 13, v_x_2748_);
lean_closure_set(v___f_2788_, 14, v___y_2749_);
lean_closure_set(v___f_2788_, 15, v___y_2756_);
v___x_2789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v_struct_2784_, v___y_2749_);
v___x_2790_ = lean_apply_4(v_toBind_2750_, lean_box(0), lean_box(0), v___x_2789_, v___f_2788_);
return v___x_2790_;
}
default: 
{
lean_object* v___x_2791_; 
lean_dec(v___f_2752_);
lean_dec_ref(v___x_2751_);
lean_dec(v_toBind_2750_);
lean_dec_ref(v_toApplicative_2737_);
v___x_2791_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_postApp_2746_, v_x_2747_, v_x_2748_, v___y_2756_, v___y_2749_);
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_toApplicative_2799_ = _args[0];
lean_object* v_inst_2800_ = _args[1];
lean_object* v_inst_2801_ = _args[2];
lean_object* v_inst_2802_ = _args[3];
lean_object* v_pre_2803_ = _args[4];
lean_object* v_post_2804_ = _args[5];
lean_object* v_usedLetOnly_2805_ = _args[6];
lean_object* v_skipConstInApp_2806_ = _args[7];
lean_object* v_skipInstances_2807_ = _args[8];
lean_object* v_postApp_2808_ = _args[9];
lean_object* v_x_2809_ = _args[10];
lean_object* v_x_2810_ = _args[11];
lean_object* v___y_2811_ = _args[12];
lean_object* v_toBind_2812_ = _args[13];
lean_object* v___x_2813_ = _args[14];
lean_object* v___f_2814_ = _args[15];
lean_object* v_e_2815_ = _args[16];
lean_object* v_a_2816_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2817_; uint8_t v_skipConstInApp_boxed_2818_; uint8_t v_skipInstances_boxed_2819_; lean_object* v_res_2820_; 
v_usedLetOnly_boxed_2817_ = lean_unbox(v_usedLetOnly_2805_);
v_skipConstInApp_boxed_2818_ = lean_unbox(v_skipConstInApp_2806_);
v_skipInstances_boxed_2819_ = lean_unbox(v_skipInstances_2807_);
v_res_2820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2799_, v_inst_2800_, v_inst_2801_, v_inst_2802_, v_pre_2803_, v_post_2804_, v_usedLetOnly_boxed_2817_, v_skipConstInApp_boxed_2818_, v_skipInstances_boxed_2819_, v_postApp_2808_, v_x_2809_, v_x_2810_, v___y_2811_, v_toBind_2812_, v___x_2813_, v___f_2814_, v_e_2815_, v_a_2816_);
lean_dec(v___y_2811_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v_toApplicative_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_pre_2825_, lean_object* v_post_2826_, uint8_t v_usedLetOnly_2827_, uint8_t v_skipConstInApp_2828_, uint8_t v_skipInstances_2829_, lean_object* v_postApp_2830_, lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_toBind_2833_, lean_object* v___x_2834_, lean_object* v___f_2835_, lean_object* v_e_2836_, lean_object* v_____r_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = lean_box(v_usedLetOnly_2827_);
v___x_2840_ = lean_box(v_skipConstInApp_2828_);
v___x_2841_ = lean_box(v_skipInstances_2829_);
lean_inc_ref(v_e_2836_);
lean_inc(v_toBind_2833_);
lean_inc(v___y_2838_);
lean_inc(v_pre_2825_);
v___f_2842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2842_, 0, v_toApplicative_2821_);
lean_closure_set(v___f_2842_, 1, v_inst_2822_);
lean_closure_set(v___f_2842_, 2, v_inst_2823_);
lean_closure_set(v___f_2842_, 3, v_inst_2824_);
lean_closure_set(v___f_2842_, 4, v_pre_2825_);
lean_closure_set(v___f_2842_, 5, v_post_2826_);
lean_closure_set(v___f_2842_, 6, v___x_2839_);
lean_closure_set(v___f_2842_, 7, v___x_2840_);
lean_closure_set(v___f_2842_, 8, v___x_2841_);
lean_closure_set(v___f_2842_, 9, v_postApp_2830_);
lean_closure_set(v___f_2842_, 10, v_x_2831_);
lean_closure_set(v___f_2842_, 11, v_x_2832_);
lean_closure_set(v___f_2842_, 12, v___y_2838_);
lean_closure_set(v___f_2842_, 13, v_toBind_2833_);
lean_closure_set(v___f_2842_, 14, v___x_2834_);
lean_closure_set(v___f_2842_, 15, v___f_2835_);
lean_closure_set(v___f_2842_, 16, v_e_2836_);
v___x_2843_ = lean_apply_1(v_pre_2825_, v_e_2836_);
v___x_2844_ = lean_apply_4(v_toBind_2833_, lean_box(0), lean_box(0), v___x_2843_, v___f_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_toApplicative_2845_ = _args[0];
lean_object* v_inst_2846_ = _args[1];
lean_object* v_inst_2847_ = _args[2];
lean_object* v_inst_2848_ = _args[3];
lean_object* v_pre_2849_ = _args[4];
lean_object* v_post_2850_ = _args[5];
lean_object* v_usedLetOnly_2851_ = _args[6];
lean_object* v_skipConstInApp_2852_ = _args[7];
lean_object* v_skipInstances_2853_ = _args[8];
lean_object* v_postApp_2854_ = _args[9];
lean_object* v_x_2855_ = _args[10];
lean_object* v_x_2856_ = _args[11];
lean_object* v_toBind_2857_ = _args[12];
lean_object* v___x_2858_ = _args[13];
lean_object* v___f_2859_ = _args[14];
lean_object* v_e_2860_ = _args[15];
lean_object* v_____r_2861_ = _args[16];
lean_object* v___y_2862_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2863_; uint8_t v_skipConstInApp_boxed_2864_; uint8_t v_skipInstances_boxed_2865_; lean_object* v_res_2866_; 
v_usedLetOnly_boxed_2863_ = lean_unbox(v_usedLetOnly_2851_);
v_skipConstInApp_boxed_2864_ = lean_unbox(v_skipConstInApp_2852_);
v_skipInstances_boxed_2865_ = lean_unbox(v_skipInstances_2853_);
v_res_2866_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v_toApplicative_2845_, v_inst_2846_, v_inst_2847_, v_inst_2848_, v_pre_2849_, v_post_2850_, v_usedLetOnly_boxed_2863_, v_skipConstInApp_boxed_2864_, v_skipInstances_boxed_2865_, v_postApp_2854_, v_x_2855_, v_x_2856_, v_toBind_2857_, v___x_2858_, v___f_2859_, v_e_2860_, v_____r_2861_, v___y_2862_);
lean_dec(v___y_2862_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_pre_2870_, lean_object* v_post_2871_, uint8_t v_usedLetOnly_2872_, uint8_t v_skipConstInApp_2873_, uint8_t v_skipInstances_2874_, lean_object* v_postApp_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_, lean_object* v_e_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___f_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v_toApplicative_2887_; lean_object* v_toBind_2888_; lean_object* v___f_2889_; lean_object* v___f_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2881_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2867_, 2);
v___x_2882_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2876_, v___x_2880_, v___x_2881_, v_inst_2867_);
v___x_2883_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2876_, v___x_2880_, v___x_2881_);
lean_inc_ref_n(v_inst_2869_, 2);
lean_inc_ref(v___x_2883_);
v___f_2884_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2884_, 0, v___x_2883_);
lean_closure_set(v___f_2884_, 1, v_inst_2869_);
v___f_2885_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2885_, 0, v___x_2883_);
lean_closure_set(v___f_2885_, 1, v_inst_2869_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___f_2884_);
lean_ctor_set(v___x_2886_, 1, v___f_2885_);
v_toApplicative_2887_ = lean_ctor_get(v_inst_2867_, 0);
lean_inc_ref_n(v_toApplicative_2887_, 5);
v_toBind_2888_ = lean_ctor_get(v_inst_2867_, 1);
lean_inc_n(v_toBind_2888_, 5);
v___f_2889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2889_, 0, v_toApplicative_2887_);
lean_inc_ref_n(v_e_2878_, 2);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2890_, 0, v_toApplicative_2887_);
lean_closure_set(v___f_2890_, 1, v___x_2880_);
lean_closure_set(v___f_2890_, 2, v___x_2881_);
lean_closure_set(v___f_2890_, 3, v_e_2878_);
lean_inc_n(v_x_2877_, 2);
lean_inc_n(v_a_2879_, 3);
v___f_2891_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2891_, 0, v_toApplicative_2887_);
lean_closure_set(v___f_2891_, 1, v___x_2880_);
lean_closure_set(v___f_2891_, 2, v___x_2881_);
lean_closure_set(v___f_2891_, 3, v_e_2878_);
lean_closure_set(v___f_2891_, 4, v_a_2879_);
lean_closure_set(v___f_2891_, 5, v_x_2877_);
lean_closure_set(v___f_2891_, 6, v_toBind_2888_);
v___x_2892_ = lean_box(v_usedLetOnly_2872_);
v___x_2893_ = lean_box(v_skipConstInApp_2873_);
v___x_2894_ = lean_box(v_skipInstances_2874_);
lean_inc_ref(v___x_2882_);
lean_inc(v_inst_2868_);
v___f_2895_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed), 18, 16);
lean_closure_set(v___f_2895_, 0, v_toApplicative_2887_);
lean_closure_set(v___f_2895_, 1, v_inst_2867_);
lean_closure_set(v___f_2895_, 2, v_inst_2868_);
lean_closure_set(v___f_2895_, 3, v_inst_2869_);
lean_closure_set(v___f_2895_, 4, v_pre_2870_);
lean_closure_set(v___f_2895_, 5, v_post_2871_);
lean_closure_set(v___f_2895_, 6, v___x_2892_);
lean_closure_set(v___f_2895_, 7, v___x_2893_);
lean_closure_set(v___f_2895_, 8, v___x_2894_);
lean_closure_set(v___f_2895_, 9, v_postApp_2875_);
lean_closure_set(v___f_2895_, 10, v_x_2876_);
lean_closure_set(v___f_2895_, 11, v_x_2877_);
lean_closure_set(v___f_2895_, 12, v_toBind_2888_);
lean_closure_set(v___f_2895_, 13, v___x_2882_);
lean_closure_set(v___f_2895_, 14, v___f_2889_);
lean_closure_set(v___f_2895_, 15, v_e_2878_);
v___f_2896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_2896_, 0, v_inst_2868_);
lean_closure_set(v___f_2896_, 1, v_x_2876_);
lean_closure_set(v___f_2896_, 2, v___x_2880_);
lean_closure_set(v___f_2896_, 3, v___x_2881_);
lean_closure_set(v___f_2896_, 4, v_inst_2867_);
lean_closure_set(v___f_2896_, 5, v___f_2895_);
lean_closure_set(v___f_2896_, 6, v___x_2886_);
lean_closure_set(v___f_2896_, 7, v___x_2882_);
lean_closure_set(v___f_2896_, 8, v_a_2879_);
lean_closure_set(v___f_2896_, 9, v_toBind_2888_);
lean_closure_set(v___f_2896_, 10, v___f_2891_);
lean_closure_set(v___f_2896_, 11, v_toApplicative_2887_);
v___x_2897_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2897_, 0, lean_box(0));
lean_closure_set(v___x_2897_, 1, lean_box(0));
lean_closure_set(v___x_2897_, 2, v_a_2879_);
v___x_2898_ = lean_apply_2(v_x_2877_, lean_box(0), v___x_2897_);
v___x_2899_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2898_, v___f_2890_);
v___x_2900_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2899_, v___f_2896_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_pre_2905_, lean_object* v_post_2906_, uint8_t v_usedLetOnly_2907_, uint8_t v_skipConstInApp_2908_, uint8_t v_skipInstances_2909_, lean_object* v_postApp_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_a_2913_, lean_object* v_e_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v___y_2917_; 
switch(lean_obj_tag(v_a_2915_))
{
case 0:
{
lean_object* v_e_2920_; lean_object* v_toPure_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v_e_2914_);
lean_dec(v_x_2912_);
lean_dec(v_postApp_2910_);
lean_dec(v_post_2906_);
lean_dec(v_pre_2905_);
lean_dec_ref(v_inst_2904_);
lean_dec(v_inst_2903_);
lean_dec_ref(v_inst_2902_);
v_e_2920_ = lean_ctor_get(v_a_2915_, 0);
lean_inc_ref(v_e_2920_);
lean_dec_ref_known(v_a_2915_, 1);
v_toPure_2921_ = lean_ctor_get(v_toApplicative_2901_, 1);
lean_inc(v_toPure_2921_);
lean_dec_ref(v_toApplicative_2901_);
v___x_2922_ = lean_apply_2(v_toPure_2921_, lean_box(0), v_e_2920_);
return v___x_2922_;
}
case 1:
{
lean_object* v_e_2923_; lean_object* v___x_2924_; 
lean_dec_ref(v_e_2914_);
lean_dec_ref(v_toApplicative_2901_);
v_e_2923_ = lean_ctor_get(v_a_2915_, 0);
lean_inc_ref(v_e_2923_);
lean_dec_ref_known(v_a_2915_, 1);
v___x_2924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2902_, v_inst_2903_, v_inst_2904_, v_pre_2905_, v_post_2906_, v_usedLetOnly_2907_, v_skipConstInApp_2908_, v_skipInstances_2909_, v_postApp_2910_, v_x_2911_, v_x_2912_, v_e_2923_, v_a_2913_);
return v___x_2924_;
}
default: 
{
lean_object* v_e_x3f_2925_; 
lean_dec(v_x_2912_);
lean_dec(v_postApp_2910_);
lean_dec(v_post_2906_);
lean_dec(v_pre_2905_);
lean_dec_ref(v_inst_2904_);
lean_dec(v_inst_2903_);
lean_dec_ref(v_inst_2902_);
v_e_x3f_2925_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_e_x3f_2925_);
lean_dec_ref_known(v_a_2915_, 1);
if (lean_obj_tag(v_e_x3f_2925_) == 0)
{
v___y_2917_ = v_e_2914_;
goto v___jp_2916_;
}
else
{
lean_object* v_val_2926_; 
lean_dec_ref(v_e_2914_);
v_val_2926_ = lean_ctor_get(v_e_x3f_2925_, 0);
lean_inc(v_val_2926_);
lean_dec_ref_known(v_e_x3f_2925_, 1);
v___y_2917_ = v_val_2926_;
goto v___jp_2916_;
}
}
}
v___jp_2916_:
{
lean_object* v_toPure_2918_; lean_object* v___x_2919_; 
v_toPure_2918_ = lean_ctor_get(v_toApplicative_2901_, 1);
lean_inc(v_toPure_2918_);
lean_dec_ref(v_toApplicative_2901_);
v___x_2919_ = lean_apply_2(v_toPure_2918_, lean_box(0), v___y_2917_);
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_pre_2931_, lean_object* v_post_2932_, lean_object* v_usedLetOnly_2933_, lean_object* v_skipConstInApp_2934_, lean_object* v_skipInstances_2935_, lean_object* v_postApp_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_, lean_object* v_a_2939_, lean_object* v_e_2940_, lean_object* v_a_2941_){
_start:
{
uint8_t v_usedLetOnly_boxed_2942_; uint8_t v_skipConstInApp_boxed_2943_; uint8_t v_skipInstances_boxed_2944_; lean_object* v_res_2945_; 
v_usedLetOnly_boxed_2942_ = lean_unbox(v_usedLetOnly_2933_);
v_skipConstInApp_boxed_2943_ = lean_unbox(v_skipConstInApp_2934_);
v_skipInstances_boxed_2944_ = lean_unbox(v_skipInstances_2935_);
v_res_2945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2927_, v_inst_2928_, v_inst_2929_, v_inst_2930_, v_pre_2931_, v_post_2932_, v_usedLetOnly_boxed_2942_, v_skipConstInApp_boxed_2943_, v_skipInstances_boxed_2944_, v_postApp_2936_, v_x_2937_, v_x_2938_, v_a_2939_, v_e_2940_, v_a_2941_);
lean_dec(v_a_2939_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_pre_2949_, lean_object* v_post_2950_, uint8_t v_usedLetOnly_2951_, uint8_t v_skipConstInApp_2952_, uint8_t v_skipInstances_2953_, lean_object* v_postApp_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_e_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_toApplicative_2959_; lean_object* v_toBind_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_toApplicative_2959_ = lean_ctor_get(v_inst_2946_, 0);
lean_inc_ref(v_toApplicative_2959_);
v_toBind_2960_ = lean_ctor_get(v_inst_2946_, 1);
lean_inc(v_toBind_2960_);
v___x_2961_ = lean_box(v_usedLetOnly_2951_);
v___x_2962_ = lean_box(v_skipConstInApp_2952_);
v___x_2963_ = lean_box(v_skipInstances_2953_);
lean_inc_ref(v_e_2957_);
lean_inc(v_a_2958_);
lean_inc(v_post_2950_);
v___f_2964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___f_2964_, 0, v_toApplicative_2959_);
lean_closure_set(v___f_2964_, 1, v_inst_2946_);
lean_closure_set(v___f_2964_, 2, v_inst_2947_);
lean_closure_set(v___f_2964_, 3, v_inst_2948_);
lean_closure_set(v___f_2964_, 4, v_pre_2949_);
lean_closure_set(v___f_2964_, 5, v_post_2950_);
lean_closure_set(v___f_2964_, 6, v___x_2961_);
lean_closure_set(v___f_2964_, 7, v___x_2962_);
lean_closure_set(v___f_2964_, 8, v___x_2963_);
lean_closure_set(v___f_2964_, 9, v_postApp_2954_);
lean_closure_set(v___f_2964_, 10, v_x_2955_);
lean_closure_set(v___f_2964_, 11, v_x_2956_);
lean_closure_set(v___f_2964_, 12, v_a_2958_);
lean_closure_set(v___f_2964_, 13, v_e_2957_);
v___x_2965_ = lean_apply_1(v_post_2950_, v_e_2957_);
v___x_2966_ = lean_apply_4(v_toBind_2960_, lean_box(0), lean_box(0), v___x_2965_, v___f_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_pre_2970_, lean_object* v_post_2971_, uint8_t v_usedLetOnly_2972_, uint8_t v_skipConstInApp_2973_, uint8_t v_skipInstances_2974_, lean_object* v_postApp_2975_, lean_object* v_x_2976_, lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2967_, v_inst_2968_, v_inst_2969_, v_pre_2970_, v_post_2971_, v_usedLetOnly_2972_, v_skipConstInApp_2973_, v_skipInstances_2974_, v_postApp_2975_, v_x_2976_, v_x_2977_, v_a_2979_, v___y_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_pre_2984_, lean_object* v_post_2985_, lean_object* v_usedLetOnly_2986_, lean_object* v_skipConstInApp_2987_, lean_object* v_skipInstances_2988_, lean_object* v_postApp_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_e_2992_, lean_object* v_a_2993_){
_start:
{
uint8_t v_usedLetOnly_boxed_2994_; uint8_t v_skipConstInApp_boxed_2995_; uint8_t v_skipInstances_boxed_2996_; lean_object* v_res_2997_; 
v_usedLetOnly_boxed_2994_ = lean_unbox(v_usedLetOnly_2986_);
v_skipConstInApp_boxed_2995_ = lean_unbox(v_skipConstInApp_2987_);
v_skipInstances_boxed_2996_ = lean_unbox(v_skipInstances_2988_);
v_res_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2981_, v_inst_2982_, v_inst_2983_, v_pre_2984_, v_post_2985_, v_usedLetOnly_boxed_2994_, v_skipConstInApp_boxed_2995_, v_skipInstances_boxed_2996_, v_postApp_2989_, v_x_2990_, v_x_2991_, v_e_2992_, v_a_2993_);
lean_dec(v_a_2993_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_pre_3001_, lean_object* v_post_3002_, lean_object* v_usedLetOnly_3003_, lean_object* v_skipConstInApp_3004_, lean_object* v_skipInstances_3005_, lean_object* v_postApp_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_fvars_3009_, lean_object* v_e_3010_, lean_object* v_a_3011_){
_start:
{
uint8_t v_usedLetOnly_boxed_3012_; uint8_t v_skipConstInApp_boxed_3013_; uint8_t v_skipInstances_boxed_3014_; lean_object* v_res_3015_; 
v_usedLetOnly_boxed_3012_ = lean_unbox(v_usedLetOnly_3003_);
v_skipConstInApp_boxed_3013_ = lean_unbox(v_skipConstInApp_3004_);
v_skipInstances_boxed_3014_ = lean_unbox(v_skipInstances_3005_);
v_res_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2998_, v_inst_2999_, v_inst_3000_, v_pre_3001_, v_post_3002_, v_usedLetOnly_boxed_3012_, v_skipConstInApp_boxed_3013_, v_skipInstances_boxed_3014_, v_postApp_3006_, v_x_3007_, v_x_3008_, v_fvars_3009_, v_e_3010_, v_a_3011_);
lean_dec(v_a_3011_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_pre_3019_, lean_object* v_post_3020_, lean_object* v_usedLetOnly_3021_, lean_object* v_skipConstInApp_3022_, lean_object* v_skipInstances_3023_, lean_object* v_postApp_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_fvars_3027_, lean_object* v_e_3028_, lean_object* v_a_3029_){
_start:
{
uint8_t v_usedLetOnly_boxed_3030_; uint8_t v_skipConstInApp_boxed_3031_; uint8_t v_skipInstances_boxed_3032_; lean_object* v_res_3033_; 
v_usedLetOnly_boxed_3030_ = lean_unbox(v_usedLetOnly_3021_);
v_skipConstInApp_boxed_3031_ = lean_unbox(v_skipConstInApp_3022_);
v_skipInstances_boxed_3032_ = lean_unbox(v_skipInstances_3023_);
v_res_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3016_, v_inst_3017_, v_inst_3018_, v_pre_3019_, v_post_3020_, v_usedLetOnly_boxed_3030_, v_skipConstInApp_boxed_3031_, v_skipInstances_boxed_3032_, v_postApp_3024_, v_x_3025_, v_x_3026_, v_fvars_3027_, v_e_3028_, v_a_3029_);
lean_dec(v_a_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_pre_3037_, lean_object* v_post_3038_, lean_object* v_usedLetOnly_3039_, lean_object* v_skipConstInApp_3040_, lean_object* v_skipInstances_3041_, lean_object* v_postApp_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_, lean_object* v_fvars_3045_, lean_object* v_e_3046_, lean_object* v_a_3047_){
_start:
{
uint8_t v_usedLetOnly_boxed_3048_; uint8_t v_skipConstInApp_boxed_3049_; uint8_t v_skipInstances_boxed_3050_; lean_object* v_res_3051_; 
v_usedLetOnly_boxed_3048_ = lean_unbox(v_usedLetOnly_3039_);
v_skipConstInApp_boxed_3049_ = lean_unbox(v_skipConstInApp_3040_);
v_skipInstances_boxed_3050_ = lean_unbox(v_skipInstances_3041_);
v_res_3051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3034_, v_inst_3035_, v_inst_3036_, v_pre_3037_, v_post_3038_, v_usedLetOnly_boxed_3048_, v_skipConstInApp_boxed_3049_, v_skipInstances_boxed_3050_, v_postApp_3042_, v_x_3043_, v_x_3044_, v_fvars_3045_, v_e_3046_, v_a_3047_);
lean_dec(v_a_3047_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_pre_3056_, lean_object* v_post_3057_, uint8_t v_usedLetOnly_3058_, uint8_t v_skipConstInApp_3059_, uint8_t v_skipInstances_3060_, lean_object* v_postApp_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_, lean_object* v_e_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3053_, v_inst_3054_, v_inst_3055_, v_pre_3056_, v_post_3057_, v_usedLetOnly_3058_, v_skipConstInApp_3059_, v_skipInstances_3060_, v_postApp_3061_, v_x_3062_, v_x_3063_, v_e_3064_, v_a_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_pre_3071_, lean_object* v_post_3072_, lean_object* v_usedLetOnly_3073_, lean_object* v_skipConstInApp_3074_, lean_object* v_skipInstances_3075_, lean_object* v_postApp_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_e_3079_, lean_object* v_a_3080_){
_start:
{
uint8_t v_usedLetOnly_boxed_3081_; uint8_t v_skipConstInApp_boxed_3082_; uint8_t v_skipInstances_boxed_3083_; lean_object* v_res_3084_; 
v_usedLetOnly_boxed_3081_ = lean_unbox(v_usedLetOnly_3073_);
v_skipConstInApp_boxed_3082_ = lean_unbox(v_skipConstInApp_3074_);
v_skipInstances_boxed_3083_ = lean_unbox(v_skipInstances_3075_);
v_res_3084_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3067_, v_inst_3068_, v_inst_3069_, v_inst_3070_, v_pre_3071_, v_post_3072_, v_usedLetOnly_boxed_3081_, v_skipConstInApp_boxed_3082_, v_skipInstances_boxed_3083_, v_postApp_3076_, v_x_3077_, v_x_3078_, v_e_3079_, v_a_3080_);
lean_dec(v_a_3080_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_pre_3089_, lean_object* v_post_3090_, uint8_t v_usedLetOnly_3091_, uint8_t v_skipConstInApp_3092_, uint8_t v_skipInstances_3093_, lean_object* v_postApp_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v_fvars_3097_, lean_object* v_e_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3086_, v_inst_3087_, v_inst_3088_, v_pre_3089_, v_post_3090_, v_usedLetOnly_3091_, v_skipConstInApp_3092_, v_skipInstances_3093_, v_postApp_3094_, v_x_3095_, v_x_3096_, v_fvars_3097_, v_e_3098_, v_a_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_pre_3105_, lean_object* v_post_3106_, lean_object* v_usedLetOnly_3107_, lean_object* v_skipConstInApp_3108_, lean_object* v_skipInstances_3109_, lean_object* v_postApp_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_fvars_3113_, lean_object* v_e_3114_, lean_object* v_a_3115_){
_start:
{
uint8_t v_usedLetOnly_boxed_3116_; uint8_t v_skipConstInApp_boxed_3117_; uint8_t v_skipInstances_boxed_3118_; lean_object* v_res_3119_; 
v_usedLetOnly_boxed_3116_ = lean_unbox(v_usedLetOnly_3107_);
v_skipConstInApp_boxed_3117_ = lean_unbox(v_skipConstInApp_3108_);
v_skipInstances_boxed_3118_ = lean_unbox(v_skipInstances_3109_);
v_res_3119_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3101_, v_inst_3102_, v_inst_3103_, v_inst_3104_, v_pre_3105_, v_post_3106_, v_usedLetOnly_boxed_3116_, v_skipConstInApp_boxed_3117_, v_skipInstances_boxed_3118_, v_postApp_3110_, v_x_3111_, v_x_3112_, v_fvars_3113_, v_e_3114_, v_a_3115_);
lean_dec(v_a_3115_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_pre_3124_, lean_object* v_post_3125_, uint8_t v_usedLetOnly_3126_, uint8_t v_skipConstInApp_3127_, uint8_t v_skipInstances_3128_, lean_object* v_postApp_3129_, lean_object* v_x_3130_, lean_object* v_x_3131_, lean_object* v_e_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3121_, v_inst_3122_, v_inst_3123_, v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3128_, v_postApp_3129_, v_x_3130_, v_x_3131_, v_e_3132_, v_a_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_pre_3139_, lean_object* v_post_3140_, lean_object* v_usedLetOnly_3141_, lean_object* v_skipConstInApp_3142_, lean_object* v_skipInstances_3143_, lean_object* v_postApp_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_, lean_object* v_e_3147_, lean_object* v_a_3148_){
_start:
{
uint8_t v_usedLetOnly_boxed_3149_; uint8_t v_skipConstInApp_boxed_3150_; uint8_t v_skipInstances_boxed_3151_; lean_object* v_res_3152_; 
v_usedLetOnly_boxed_3149_ = lean_unbox(v_usedLetOnly_3141_);
v_skipConstInApp_boxed_3150_ = lean_unbox(v_skipConstInApp_3142_);
v_skipInstances_boxed_3151_ = lean_unbox(v_skipInstances_3143_);
v_res_3152_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3135_, v_inst_3136_, v_inst_3137_, v_inst_3138_, v_pre_3139_, v_post_3140_, v_usedLetOnly_boxed_3149_, v_skipConstInApp_boxed_3150_, v_skipInstances_boxed_3151_, v_postApp_3144_, v_x_3145_, v_x_3146_, v_e_3147_, v_a_3148_);
lean_dec(v_a_3148_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_pre_3157_, lean_object* v_post_3158_, uint8_t v_usedLetOnly_3159_, uint8_t v_skipConstInApp_3160_, uint8_t v_skipInstances_3161_, lean_object* v_postApp_3162_, lean_object* v_x_3163_, lean_object* v_x_3164_, lean_object* v_fvars_3165_, lean_object* v_e_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3154_, v_inst_3155_, v_inst_3156_, v_pre_3157_, v_post_3158_, v_usedLetOnly_3159_, v_skipConstInApp_3160_, v_skipInstances_3161_, v_postApp_3162_, v_x_3163_, v_x_3164_, v_fvars_3165_, v_e_3166_, v_a_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_pre_3173_, lean_object* v_post_3174_, lean_object* v_usedLetOnly_3175_, lean_object* v_skipConstInApp_3176_, lean_object* v_skipInstances_3177_, lean_object* v_postApp_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_, lean_object* v_fvars_3181_, lean_object* v_e_3182_, lean_object* v_a_3183_){
_start:
{
uint8_t v_usedLetOnly_boxed_3184_; uint8_t v_skipConstInApp_boxed_3185_; uint8_t v_skipInstances_boxed_3186_; lean_object* v_res_3187_; 
v_usedLetOnly_boxed_3184_ = lean_unbox(v_usedLetOnly_3175_);
v_skipConstInApp_boxed_3185_ = lean_unbox(v_skipConstInApp_3176_);
v_skipInstances_boxed_3186_ = lean_unbox(v_skipInstances_3177_);
v_res_3187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3169_, v_inst_3170_, v_inst_3171_, v_inst_3172_, v_pre_3173_, v_post_3174_, v_usedLetOnly_boxed_3184_, v_skipConstInApp_boxed_3185_, v_skipInstances_boxed_3186_, v_postApp_3178_, v_x_3179_, v_x_3180_, v_fvars_3181_, v_e_3182_, v_a_3183_);
lean_dec(v_a_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_pre_3192_, lean_object* v_post_3193_, uint8_t v_usedLetOnly_3194_, uint8_t v_skipConstInApp_3195_, uint8_t v_skipInstances_3196_, lean_object* v_postApp_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_, lean_object* v_fvars_3200_, lean_object* v_e_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3189_, v_inst_3190_, v_inst_3191_, v_pre_3192_, v_post_3193_, v_usedLetOnly_3194_, v_skipConstInApp_3195_, v_skipInstances_3196_, v_postApp_3197_, v_x_3198_, v_x_3199_, v_fvars_3200_, v_e_3201_, v_a_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3204_, lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_pre_3208_, lean_object* v_post_3209_, lean_object* v_usedLetOnly_3210_, lean_object* v_skipConstInApp_3211_, lean_object* v_skipInstances_3212_, lean_object* v_postApp_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_, lean_object* v_fvars_3216_, lean_object* v_e_3217_, lean_object* v_a_3218_){
_start:
{
uint8_t v_usedLetOnly_boxed_3219_; uint8_t v_skipConstInApp_boxed_3220_; uint8_t v_skipInstances_boxed_3221_; lean_object* v_res_3222_; 
v_usedLetOnly_boxed_3219_ = lean_unbox(v_usedLetOnly_3210_);
v_skipConstInApp_boxed_3220_ = lean_unbox(v_skipConstInApp_3211_);
v_skipInstances_boxed_3221_ = lean_unbox(v_skipInstances_3212_);
v_res_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3204_, v_inst_3205_, v_inst_3206_, v_inst_3207_, v_pre_3208_, v_post_3209_, v_usedLetOnly_boxed_3219_, v_skipConstInApp_boxed_3220_, v_skipInstances_boxed_3221_, v_postApp_3213_, v_x_3214_, v_x_3215_, v_fvars_3216_, v_e_3217_, v_a_3218_);
lean_dec(v_a_3218_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_apply_1(v_x_3223_, lean_box(0));
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3238_, lean_object* v_00_u03b1_3239_, lean_object* v_x_3240_){
_start:
{
lean_object* v___f_3241_; lean_object* v___x_3242_; 
v___f_3241_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3241_, 0, v_x_3240_);
v___x_3242_ = lean_apply_2(v_inst_3238_, lean_box(0), v___f_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3243_, lean_object* v_x_3244_, lean_object* v_toBind_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_pre_3249_, lean_object* v_post_3250_, uint8_t v_usedLetOnly_3251_, uint8_t v_skipConstInApp_3252_, uint8_t v_skipInstances_3253_, lean_object* v_postApp_3254_, lean_object* v_x_3255_, lean_object* v_input_3256_, lean_object* v_ref_3257_){
_start:
{
lean_object* v___f_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_inc(v_toBind_3245_);
lean_inc(v_x_3244_);
lean_inc(v_ref_3257_);
v___f_3258_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3258_, 0, v_toPure_3243_);
lean_closure_set(v___f_3258_, 1, v_ref_3257_);
lean_closure_set(v___f_3258_, 2, v_x_3244_);
lean_closure_set(v___f_3258_, 3, v_toBind_3245_);
v___x_3259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3246_, v_inst_3247_, v_inst_3248_, v_pre_3249_, v_post_3250_, v_usedLetOnly_3251_, v_skipConstInApp_3252_, v_skipInstances_3253_, v_postApp_3254_, v_x_3255_, v_x_3244_, v_input_3256_, v_ref_3257_);
lean_dec(v_ref_3257_);
v___x_3260_ = lean_apply_4(v_toBind_3245_, lean_box(0), lean_box(0), v___x_3259_, v___f_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3261_, lean_object* v_x_3262_, lean_object* v_toBind_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_pre_3267_, lean_object* v_post_3268_, lean_object* v_usedLetOnly_3269_, lean_object* v_skipConstInApp_3270_, lean_object* v_skipInstances_3271_, lean_object* v_postApp_3272_, lean_object* v_x_3273_, lean_object* v_input_3274_, lean_object* v_ref_3275_){
_start:
{
uint8_t v_usedLetOnly_boxed_3276_; uint8_t v_skipConstInApp_boxed_3277_; uint8_t v_skipInstances_boxed_3278_; lean_object* v_res_3279_; 
v_usedLetOnly_boxed_3276_ = lean_unbox(v_usedLetOnly_3269_);
v_skipConstInApp_boxed_3277_ = lean_unbox(v_skipConstInApp_3270_);
v_skipInstances_boxed_3278_ = lean_unbox(v_skipInstances_3271_);
v_res_3279_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3261_, v_x_3262_, v_toBind_3263_, v_inst_3264_, v_inst_3265_, v_inst_3266_, v_pre_3267_, v_post_3268_, v_usedLetOnly_boxed_3276_, v_skipConstInApp_boxed_3277_, v_skipInstances_boxed_3278_, v_postApp_3272_, v_x_3273_, v_input_3274_, v_ref_3275_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_input_3283_, lean_object* v_cache_3284_, lean_object* v_pre_3285_, lean_object* v_post_3286_, uint8_t v_usedLetOnly_3287_, uint8_t v_skipConstInApp_3288_, uint8_t v_skipInstances_3289_, lean_object* v_postApp_3290_){
_start:
{
lean_object* v_x_3291_; lean_object* v_toApplicative_3292_; lean_object* v_toBind_3293_; lean_object* v_toPure_3294_; lean_object* v_x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___f_3301_; lean_object* v___x_3302_; 
v_x_3291_ = lean_box(0);
v_toApplicative_3292_ = lean_ctor_get(v_inst_3280_, 0);
v_toBind_3293_ = lean_ctor_get(v_inst_3280_, 1);
lean_inc_n(v_toBind_3293_, 2);
v_toPure_3294_ = lean_ctor_get(v_toApplicative_3292_, 1);
lean_inc(v_toPure_3294_);
lean_inc_n(v_inst_3281_, 2);
v_x_3295_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3295_, 0, v_inst_3281_);
v___x_3296_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3296_, 0, lean_box(0));
lean_closure_set(v___x_3296_, 1, lean_box(0));
lean_closure_set(v___x_3296_, 2, v_cache_3284_);
v___x_3297_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3281_, lean_box(0), v___x_3296_);
v___x_3298_ = lean_box(v_usedLetOnly_3287_);
v___x_3299_ = lean_box(v_skipConstInApp_3288_);
v___x_3300_ = lean_box(v_skipInstances_3289_);
v___f_3301_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3301_, 0, v_toPure_3294_);
lean_closure_set(v___f_3301_, 1, v_x_3295_);
lean_closure_set(v___f_3301_, 2, v_toBind_3293_);
lean_closure_set(v___f_3301_, 3, v_inst_3280_);
lean_closure_set(v___f_3301_, 4, v_inst_3281_);
lean_closure_set(v___f_3301_, 5, v_inst_3282_);
lean_closure_set(v___f_3301_, 6, v_pre_3285_);
lean_closure_set(v___f_3301_, 7, v_post_3286_);
lean_closure_set(v___f_3301_, 8, v___x_3298_);
lean_closure_set(v___f_3301_, 9, v___x_3299_);
lean_closure_set(v___f_3301_, 10, v___x_3300_);
lean_closure_set(v___f_3301_, 11, v_postApp_3290_);
lean_closure_set(v___f_3301_, 12, v_x_3291_);
lean_closure_set(v___f_3301_, 13, v_input_3283_);
v___x_3302_ = lean_apply_4(v_toBind_3293_, lean_box(0), lean_box(0), v___x_3297_, v___f_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_input_3306_, lean_object* v_cache_3307_, lean_object* v_pre_3308_, lean_object* v_post_3309_, lean_object* v_usedLetOnly_3310_, lean_object* v_skipConstInApp_3311_, lean_object* v_skipInstances_3312_, lean_object* v_postApp_3313_){
_start:
{
uint8_t v_usedLetOnly_boxed_3314_; uint8_t v_skipConstInApp_boxed_3315_; uint8_t v_skipInstances_boxed_3316_; lean_object* v_res_3317_; 
v_usedLetOnly_boxed_3314_ = lean_unbox(v_usedLetOnly_3310_);
v_skipConstInApp_boxed_3315_ = lean_unbox(v_skipConstInApp_3311_);
v_skipInstances_boxed_3316_ = lean_unbox(v_skipInstances_3312_);
v_res_3317_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3303_, v_inst_3304_, v_inst_3305_, v_input_3306_, v_cache_3307_, v_pre_3308_, v_post_3309_, v_usedLetOnly_boxed_3314_, v_skipConstInApp_boxed_3315_, v_skipInstances_boxed_3316_, v_postApp_3313_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_input_3322_, lean_object* v_cache_3323_, lean_object* v_pre_3324_, lean_object* v_post_3325_, uint8_t v_usedLetOnly_3326_, uint8_t v_skipConstInApp_3327_, uint8_t v_skipInstances_3328_, lean_object* v_postApp_3329_){
_start:
{
lean_object* v_x_3330_; lean_object* v_toApplicative_3331_; lean_object* v_toBind_3332_; lean_object* v_toPure_3333_; lean_object* v_x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; lean_object* v___x_3341_; 
v_x_3330_ = lean_box(0);
v_toApplicative_3331_ = lean_ctor_get(v_inst_3319_, 0);
v_toBind_3332_ = lean_ctor_get(v_inst_3319_, 1);
lean_inc_n(v_toBind_3332_, 2);
v_toPure_3333_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc(v_toPure_3333_);
lean_inc_n(v_inst_3320_, 2);
v_x_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3334_, 0, v_inst_3320_);
v___x_3335_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3335_, 0, lean_box(0));
lean_closure_set(v___x_3335_, 1, lean_box(0));
lean_closure_set(v___x_3335_, 2, v_cache_3323_);
v___x_3336_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3320_, lean_box(0), v___x_3335_);
v___x_3337_ = lean_box(v_usedLetOnly_3326_);
v___x_3338_ = lean_box(v_skipConstInApp_3327_);
v___x_3339_ = lean_box(v_skipInstances_3328_);
v___f_3340_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3340_, 0, v_toPure_3333_);
lean_closure_set(v___f_3340_, 1, v_x_3334_);
lean_closure_set(v___f_3340_, 2, v_toBind_3332_);
lean_closure_set(v___f_3340_, 3, v_inst_3319_);
lean_closure_set(v___f_3340_, 4, v_inst_3320_);
lean_closure_set(v___f_3340_, 5, v_inst_3321_);
lean_closure_set(v___f_3340_, 6, v_pre_3324_);
lean_closure_set(v___f_3340_, 7, v_post_3325_);
lean_closure_set(v___f_3340_, 8, v___x_3337_);
lean_closure_set(v___f_3340_, 9, v___x_3338_);
lean_closure_set(v___f_3340_, 10, v___x_3339_);
lean_closure_set(v___f_3340_, 11, v_postApp_3329_);
lean_closure_set(v___f_3340_, 12, v_x_3330_);
lean_closure_set(v___f_3340_, 13, v_input_3322_);
v___x_3341_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v___x_3336_, v___f_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_input_3346_, lean_object* v_cache_3347_, lean_object* v_pre_3348_, lean_object* v_post_3349_, lean_object* v_usedLetOnly_3350_, lean_object* v_skipConstInApp_3351_, lean_object* v_skipInstances_3352_, lean_object* v_postApp_3353_){
_start:
{
uint8_t v_usedLetOnly_boxed_3354_; uint8_t v_skipConstInApp_boxed_3355_; uint8_t v_skipInstances_boxed_3356_; lean_object* v_res_3357_; 
v_usedLetOnly_boxed_3354_ = lean_unbox(v_usedLetOnly_3350_);
v_skipConstInApp_boxed_3355_ = lean_unbox(v_skipConstInApp_3351_);
v_skipInstances_boxed_3356_ = lean_unbox(v_skipInstances_3352_);
v_res_3357_ = l_Lean_Meta_transformWithCache(v_m_3342_, v_inst_3343_, v_inst_3344_, v_inst_3345_, v_input_3346_, v_cache_3347_, v_pre_3348_, v_post_3349_, v_usedLetOnly_boxed_3354_, v_skipConstInApp_boxed_3355_, v_skipInstances_boxed_3356_, v_postApp_3353_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2(lean_object* v_toPure_3358_, lean_object* v_x_3359_, lean_object* v_e_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_apply_2(v_toPure_3358_, lean_box(0), v_e_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2___boxed(lean_object* v_toPure_3362_, lean_object* v_x_3363_, lean_object* v_e_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Meta_transform___redArg___lam__2(v_toPure_3362_, v_x_3363_, v_e_3364_);
lean_dec_ref(v_x_3363_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4(lean_object* v_toPure_3366_, lean_object* v_x_3367_, lean_object* v_toBind_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_pre_3372_, lean_object* v_post_3373_, uint8_t v_usedLetOnly_3374_, uint8_t v_skipConstInApp_3375_, uint8_t v___x_3376_, lean_object* v___f_3377_, lean_object* v_x_3378_, lean_object* v_input_3379_, lean_object* v_ref_3380_){
_start:
{
lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_inc(v_toBind_3368_);
lean_inc(v_x_3367_);
lean_inc(v_ref_3380_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3381_, 0, v_toPure_3366_);
lean_closure_set(v___f_3381_, 1, v_ref_3380_);
lean_closure_set(v___f_3381_, 2, v_x_3367_);
lean_closure_set(v___f_3381_, 3, v_toBind_3368_);
v___x_3382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3369_, v_inst_3370_, v_inst_3371_, v_pre_3372_, v_post_3373_, v_usedLetOnly_3374_, v_skipConstInApp_3375_, v___x_3376_, v___f_3377_, v_x_3378_, v_x_3367_, v_input_3379_, v_ref_3380_);
lean_dec(v_ref_3380_);
v___x_3383_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3382_, v___f_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4___boxed(lean_object* v_toPure_3384_, lean_object* v_x_3385_, lean_object* v_toBind_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_pre_3390_, lean_object* v_post_3391_, lean_object* v_usedLetOnly_3392_, lean_object* v_skipConstInApp_3393_, lean_object* v___x_3394_, lean_object* v___f_3395_, lean_object* v_x_3396_, lean_object* v_input_3397_, lean_object* v_ref_3398_){
_start:
{
uint8_t v_usedLetOnly_boxed_3399_; uint8_t v_skipConstInApp_boxed_3400_; uint8_t v___x_129__boxed_3401_; lean_object* v_res_3402_; 
v_usedLetOnly_boxed_3399_ = lean_unbox(v_usedLetOnly_3392_);
v_skipConstInApp_boxed_3400_ = lean_unbox(v_skipConstInApp_3393_);
v___x_129__boxed_3401_ = lean_unbox(v___x_3394_);
v_res_3402_ = l_Lean_Meta_transform___redArg___lam__4(v_toPure_3384_, v_x_3385_, v_toBind_3386_, v_inst_3387_, v_inst_3388_, v_inst_3389_, v_pre_3390_, v_post_3391_, v_usedLetOnly_boxed_3399_, v_skipConstInApp_boxed_3400_, v___x_129__boxed_3401_, v___f_3395_, v_x_3396_, v_input_3397_, v_ref_3398_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_input_3406_, lean_object* v_pre_3407_, lean_object* v_post_3408_, uint8_t v_usedLetOnly_3409_, uint8_t v_skipConstInApp_3410_){
_start:
{
lean_object* v_toApplicative_3411_; lean_object* v_toBind_3412_; lean_object* v_toPure_3413_; lean_object* v_x_3414_; uint8_t v___x_3415_; lean_object* v___f_3416_; lean_object* v___f_3417_; lean_object* v_x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_toApplicative_3411_ = lean_ctor_get(v_inst_3403_, 0);
v_toBind_3412_ = lean_ctor_get(v_inst_3403_, 1);
lean_inc_n(v_toBind_3412_, 3);
v_toPure_3413_ = lean_ctor_get(v_toApplicative_3411_, 1);
lean_inc_n(v_toPure_3413_, 3);
lean_inc_n(v_inst_3404_, 2);
v_x_3414_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3414_, 0, v_inst_3404_);
v___x_3415_ = 0;
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3416_, 0, v_toPure_3413_);
v___f_3417_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3417_, 0, v_toPure_3413_);
v_x_3418_ = lean_box(0);
v___x_3419_ = lean_box(v_usedLetOnly_3409_);
v___x_3420_ = lean_box(v_skipConstInApp_3410_);
v___x_3421_ = lean_box(v___x_3415_);
v___f_3422_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3422_, 0, v_toPure_3413_);
lean_closure_set(v___f_3422_, 1, v_x_3414_);
lean_closure_set(v___f_3422_, 2, v_toBind_3412_);
lean_closure_set(v___f_3422_, 3, v_inst_3403_);
lean_closure_set(v___f_3422_, 4, v_inst_3404_);
lean_closure_set(v___f_3422_, 5, v_inst_3405_);
lean_closure_set(v___f_3422_, 6, v_pre_3407_);
lean_closure_set(v___f_3422_, 7, v_post_3408_);
lean_closure_set(v___f_3422_, 8, v___x_3419_);
lean_closure_set(v___f_3422_, 9, v___x_3420_);
lean_closure_set(v___f_3422_, 10, v___x_3421_);
lean_closure_set(v___f_3422_, 11, v___f_3416_);
lean_closure_set(v___f_3422_, 12, v_x_3418_);
lean_closure_set(v___f_3422_, 13, v_input_3406_);
v___x_3423_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3424_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3404_, lean_box(0), v___x_3423_);
v___x_3425_ = lean_apply_4(v_toBind_3412_, lean_box(0), lean_box(0), v___x_3424_, v___f_3422_);
v___x_3426_ = lean_apply_4(v_toBind_3412_, lean_box(0), lean_box(0), v___x_3425_, v___f_3417_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3427_, lean_object* v_inst_3428_, lean_object* v_inst_3429_, lean_object* v_input_3430_, lean_object* v_pre_3431_, lean_object* v_post_3432_, lean_object* v_usedLetOnly_3433_, lean_object* v_skipConstInApp_3434_){
_start:
{
uint8_t v_usedLetOnly_boxed_3435_; uint8_t v_skipConstInApp_boxed_3436_; lean_object* v_res_3437_; 
v_usedLetOnly_boxed_3435_ = lean_unbox(v_usedLetOnly_3433_);
v_skipConstInApp_boxed_3436_ = lean_unbox(v_skipConstInApp_3434_);
v_res_3437_ = l_Lean_Meta_transform___redArg(v_inst_3427_, v_inst_3428_, v_inst_3429_, v_input_3430_, v_pre_3431_, v_post_3432_, v_usedLetOnly_boxed_3435_, v_skipConstInApp_boxed_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_inst_3441_, lean_object* v_input_3442_, lean_object* v_pre_3443_, lean_object* v_post_3444_, uint8_t v_usedLetOnly_3445_, uint8_t v_skipConstInApp_3446_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Lean_Meta_transform___redArg(v_inst_3439_, v_inst_3440_, v_inst_3441_, v_input_3442_, v_pre_3443_, v_post_3444_, v_usedLetOnly_3445_, v_skipConstInApp_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_input_3452_, lean_object* v_pre_3453_, lean_object* v_post_3454_, lean_object* v_usedLetOnly_3455_, lean_object* v_skipConstInApp_3456_){
_start:
{
uint8_t v_usedLetOnly_boxed_3457_; uint8_t v_skipConstInApp_boxed_3458_; lean_object* v_res_3459_; 
v_usedLetOnly_boxed_3457_ = lean_unbox(v_usedLetOnly_3455_);
v_skipConstInApp_boxed_3458_ = lean_unbox(v_skipConstInApp_3456_);
v_res_3459_ = l_Lean_Meta_transform(v_m_3448_, v_inst_3449_, v_inst_3450_, v_inst_3451_, v_input_3452_, v_pre_3453_, v_post_3454_, v_usedLetOnly_boxed_3457_, v_skipConstInApp_boxed_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3460_, lean_object* v___y_3461_){
_start:
{
uint8_t v___x_3463_; 
v___x_3463_ = l_Lean_Expr_hasMVar(v_e_3460_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_e_3460_);
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; lean_object* v_mctx_3466_; lean_object* v___x_3467_; lean_object* v_fst_3468_; lean_object* v_snd_3469_; lean_object* v___x_3470_; lean_object* v_cache_3471_; lean_object* v_zetaDeltaFVarIds_3472_; lean_object* v_postponed_3473_; lean_object* v_diag_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3483_; 
v___x_3465_ = lean_st_ref_get(v___y_3461_);
v_mctx_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc_ref(v_mctx_3466_);
lean_dec(v___x_3465_);
v___x_3467_ = l_Lean_instantiateMVarsCore(v_mctx_3466_, v_e_3460_);
v_fst_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_fst_3468_);
v_snd_3469_ = lean_ctor_get(v___x_3467_, 1);
lean_inc(v_snd_3469_);
lean_dec_ref(v___x_3467_);
v___x_3470_ = lean_st_ref_take(v___y_3461_);
v_cache_3471_ = lean_ctor_get(v___x_3470_, 1);
v_zetaDeltaFVarIds_3472_ = lean_ctor_get(v___x_3470_, 2);
v_postponed_3473_ = lean_ctor_get(v___x_3470_, 3);
v_diag_3474_ = lean_ctor_get(v___x_3470_, 4);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3470_, 0);
lean_dec(v_unused_3484_);
v___x_3476_ = v___x_3470_;
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_diag_3474_);
lean_inc(v_postponed_3473_);
lean_inc(v_zetaDeltaFVarIds_3472_);
lean_inc(v_cache_3471_);
lean_dec(v___x_3470_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3483_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_snd_3469_);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_snd_3469_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_cache_3471_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_zetaDeltaFVarIds_3472_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_postponed_3473_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v_diag_3474_);
v___x_3479_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_st_ref_put(v___y_3461_, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_fst_3468_);
return v___x_3481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3485_, v___y_3486_);
lean_dec(v___y_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3489_, v___y_3491_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3503_, lean_object* v___x_3504_, uint8_t v_zetaDelta_3505_, lean_object* v_fvarId_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3541_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3541_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3541_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
if (lean_obj_tag(v_a_3513_) == 1)
{
lean_object* v_val_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3536_; 
v_val_3517_ = lean_ctor_get(v_a_3513_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3513_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3519_ = v_a_3513_;
v_isShared_3520_ = v_isSharedCheck_3536_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_val_3517_);
lean_dec(v_a_3513_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3536_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
uint8_t v___y_3522_; 
if (v_zetaDelta_3505_ == 0)
{
lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3530_ = l_Lean_LocalDecl_index(v_val_3517_);
v___x_3531_ = lean_nat_dec_lt(v___x_3530_, v___x_3504_);
lean_dec(v___x_3530_);
if (v___x_3531_ == 0)
{
lean_del_object(v___x_3519_);
goto v___jp_3527_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
lean_dec(v_val_3517_);
lean_del_object(v___x_3515_);
v___x_3532_ = lean_box(0);
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3532_);
v___x_3534_ = v___x_3519_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
else
{
lean_del_object(v___x_3519_);
goto v___jp_3527_;
}
v___jp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = l_Lean_LocalDecl_value_x3f(v_val_3517_, v___y_3522_);
lean_dec(v_val_3517_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3523_);
v___x_3525_ = v___x_3515_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
v___jp_3527_:
{
if (v_zetaHave_3503_ == 0)
{
v___y_3522_ = v_zetaHave_3503_;
goto v___jp_3521_;
}
else
{
lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3528_ = l_Lean_LocalDecl_index(v_val_3517_);
v___x_3529_ = lean_nat_dec_le(v___x_3504_, v___x_3528_);
lean_dec(v___x_3528_);
v___y_3522_ = v___x_3529_;
goto v___jp_3521_;
}
}
}
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
lean_dec(v_a_3513_);
v___x_3537_ = lean_box(0);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3537_);
v___x_3539_ = v___x_3515_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
v_a_3542_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3512_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3512_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3550_, lean_object* v___x_3551_, lean_object* v_zetaDelta_3552_, lean_object* v_fvarId_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
uint8_t v_zetaHave_boxed_3559_; uint8_t v_zetaDelta_boxed_3560_; lean_object* v_res_3561_; 
v_zetaHave_boxed_3559_ = lean_unbox(v_zetaHave_3550_);
v_zetaDelta_boxed_3560_ = lean_unbox(v_zetaDelta_3552_);
v_res_3561_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3559_, v___x_3551_, v_zetaDelta_boxed_3560_, v_fvarId_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___x_3551_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_e_3562_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3577_, lean_object* v_e_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
if (lean_obj_tag(v_e_3578_) == 1)
{
lean_object* v_fvarId_3584_; lean_object* v___x_3585_; 
v_fvarId_3584_ = lean_ctor_get(v_e_3578_, 0);
lean_inc(v___y_3582_);
lean_inc_ref(v___y_3581_);
lean_inc(v___y_3580_);
lean_inc_ref(v___y_3579_);
lean_inc(v_fvarId_3584_);
v___x_3585_ = lean_apply_6(v___f_3577_, v_fvarId_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, lean_box(0));
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3611_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3611_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3611_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
if (lean_obj_tag(v_a_3586_) == 1)
{
lean_object* v_val_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3606_; 
lean_del_object(v___x_3588_);
lean_dec_ref_known(v_e_3578_, 1);
v_val_3590_ = lean_ctor_get(v_a_3586_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3586_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3592_ = v_a_3586_;
v_isShared_3593_ = v_isSharedCheck_3606_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_val_3590_);
lean_dec(v_a_3586_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3606_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3605_; 
v___x_3594_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3590_, v___y_3580_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v_a_3595_);
v___x_3600_ = v___x_3592_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3600_);
v___x_3602_ = v___x_3597_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_dec(v_a_3586_);
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v_e_3578_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3607_);
v___x_3609_ = v___x_3588_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec_ref_known(v_e_3578_, 1);
v_a_3612_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3585_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3585_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_dec_ref(v_e_3578_);
lean_dec_ref(v___f_3577_);
v___x_3620_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3622_, lean_object* v_e_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3622_, v_e_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3630_, lean_object* v_e_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Expr_getAppFn(v_e_3631_);
if (lean_obj_tag(v___x_3637_) == 1)
{
lean_object* v_fvarId_3638_; lean_object* v___x_3639_; 
v_fvarId_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_fvarId_3638_);
lean_dec_ref_known(v___x_3637_, 1);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
lean_inc(v___y_3633_);
lean_inc_ref(v___y_3632_);
v___x_3639_ = lean_apply_6(v___f_3630_, v_fvarId_3638_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, lean_box(0));
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3672_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3672_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3672_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
if (lean_obj_tag(v_a_3640_) == 1)
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3667_; 
lean_del_object(v___x_3642_);
v_val_3644_ = lean_ctor_get(v_a_3640_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3646_ = v_a_3640_;
v_isShared_3647_ = v_isSharedCheck_3667_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v_a_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3667_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3666_; 
v___x_3648_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3644_, v___y_3633_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3666_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3666_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_dummy_3653_; lean_object* v_nargs_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v_dummy_3653_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_3654_ = l_Lean_Expr_getAppNumArgs(v_e_3631_);
lean_inc(v_nargs_3654_);
v___x_3655_ = lean_mk_array(v_nargs_3654_, v_dummy_3653_);
v___x_3656_ = lean_unsigned_to_nat(1u);
v___x_3657_ = lean_nat_sub(v_nargs_3654_, v___x_3656_);
lean_dec(v_nargs_3654_);
v___x_3658_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3631_, v___x_3655_, v___x_3657_);
v___x_3659_ = l_Lean_Expr_beta(v_a_3649_, v___x_3658_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3659_);
v___x_3661_ = v___x_3646_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3661_);
v___x_3663_ = v___x_3651_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_dec(v_a_3640_);
lean_dec_ref(v_e_3631_);
v___x_3668_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3668_);
v___x_3670_ = v___x_3642_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec_ref(v_e_3631_);
v_a_3673_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3639_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3639_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v___x_3637_);
lean_dec_ref(v_e_3631_);
lean_dec_ref(v___f_3630_);
v___x_3681_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3683_, lean_object* v_e_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3683_, v_e_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3691_, lean_object* v_x_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_apply_1(v_x_3692_, lean_box(0));
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3700_, v_x_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3708_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3722_, lean_object* v___y_3723_, lean_object* v_b_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
lean_inc(v___y_3728_);
lean_inc_ref(v___y_3727_);
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3723_);
v___x_3730_ = lean_apply_7(v_k_3722_, v_b_3724_, v___y_3723_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, lean_box(0));
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3731_, lean_object* v___y_3732_, lean_object* v_b_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3731_, v___y_3732_, v_b_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3732_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3740_, uint8_t v_bi_3741_, lean_object* v_type_3742_, lean_object* v_k_3743_, uint8_t v_kind_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___f_3751_; lean_object* v___x_3752_; 
lean_inc(v___y_3745_);
v___f_3751_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3751_, 0, v_k_3743_);
lean_closure_set(v___f_3751_, 1, v___y_3745_);
v___x_3752_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3740_, v_bi_3741_, v_type_3742_, v___f_3751_, v_kind_3744_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3752_) == 0)
{
return v___x_3752_;
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3761_, lean_object* v_bi_3762_, lean_object* v_type_3763_, lean_object* v_k_3764_, lean_object* v_kind_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v_bi_boxed_3772_; uint8_t v_kind_boxed_3773_; lean_object* v_res_3774_; 
v_bi_boxed_3772_ = lean_unbox(v_bi_3762_);
v_kind_boxed_3773_ = lean_unbox(v_kind_3765_);
v_res_3774_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3761_, v_bi_boxed_3772_, v_type_3763_, v_k_3764_, v_kind_boxed_3773_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3775_, lean_object* v_type_3776_, lean_object* v_val_3777_, lean_object* v_k_3778_, uint8_t v_nondep_3779_, uint8_t v_kind_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v___f_3787_; lean_object* v___x_3788_; 
lean_inc(v___y_3781_);
v___f_3787_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3787_, 0, v_k_3778_);
lean_closure_set(v___f_3787_, 1, v___y_3781_);
v___x_3788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3775_, v_type_3776_, v_val_3777_, v___f_3787_, v_nondep_3779_, v_kind_3780_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3788_) == 0)
{
return v___x_3788_;
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3797_, lean_object* v_type_3798_, lean_object* v_val_3799_, lean_object* v_k_3800_, lean_object* v_nondep_3801_, lean_object* v_kind_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v_nondep_boxed_3809_; uint8_t v_kind_boxed_3810_; lean_object* v_res_3811_; 
v_nondep_boxed_3809_ = lean_unbox(v_nondep_3801_);
v_kind_boxed_3810_ = lean_unbox(v_kind_3802_);
v_res_3811_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3797_, v_type_3798_, v_val_3799_, v_k_3800_, v_nondep_boxed_3809_, v_kind_boxed_3810_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_apply_1(v_x_3813_, lean_box(0));
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3821_, v_x_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v_ref_3829_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___y_3845_; lean_object* v_toCold_3854_; lean_object* v_currRecDepth_3855_; lean_object* v_ref_3856_; uint16_t v_optionFlags_3857_; uint8_t v_suppressElabErrors_3858_; uint8_t v_checkDeprecated_3859_; uint8_t v_isRecordingDeps_3860_; lean_object* v_maxRecDepth_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v_toCold_3854_ = lean_ctor_get(v___y_3841_, 0);
v_currRecDepth_3855_ = lean_ctor_get(v___y_3841_, 1);
v_ref_3856_ = lean_ctor_get(v___y_3841_, 2);
v_optionFlags_3857_ = lean_ctor_get_uint16(v___y_3841_, sizeof(void*)*3);
v_suppressElabErrors_3858_ = lean_ctor_get_uint8(v___y_3841_, sizeof(void*)*3 + 2);
v_checkDeprecated_3859_ = lean_ctor_get_uint8(v___y_3841_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3860_ = lean_ctor_get_uint8(v___y_3841_, sizeof(void*)*3 + 4);
v_maxRecDepth_3866_ = lean_ctor_get(v_toCold_3854_, 3);
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = lean_nat_dec_eq(v_maxRecDepth_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_nat_dec_eq(v_currRecDepth_3855_, v_maxRecDepth_3866_);
if (v___x_3869_ == 0)
{
goto v___jp_3861_;
}
else
{
lean_object* v___x_3870_; 
lean_dec_ref(v_x_3837_);
lean_inc(v_ref_3856_);
v___x_3870_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3856_);
v___y_3845_ = v___x_3870_;
goto v___jp_3844_;
}
}
else
{
goto v___jp_3861_;
}
v___jp_3844_:
{
if (lean_obj_tag(v___y_3845_) == 0)
{
return v___y_3845_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___y_3845_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___y_3845_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___y_3845_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___y_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
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
v___jp_3861_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = lean_nat_add(v_currRecDepth_3855_, v___x_3862_);
lean_inc(v_ref_3856_);
lean_inc_ref(v_toCold_3854_);
v___x_3864_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3864_, 0, v_toCold_3854_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
lean_ctor_set(v___x_3864_, 2, v_ref_3856_);
lean_ctor_set_uint16(v___x_3864_, sizeof(void*)*3, v_optionFlags_3857_);
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*3 + 2, v_suppressElabErrors_3858_);
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*3 + 3, v_checkDeprecated_3859_);
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*3 + 4, v_isRecordingDeps_3860_);
lean_inc(v___y_3842_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc(v___y_3838_);
v___x_3865_ = lean_apply_6(v_x_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___x_3864_, v___y_3842_, lean_box(0));
v___y_3845_ = v___x_3865_;
goto v___jp_3844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3879_, lean_object* v_pre_3880_, lean_object* v_post_3881_, lean_object* v_usedLetOnly_3882_, lean_object* v_skipConstInApp_3883_, lean_object* v_skipInstances_3884_, lean_object* v_postApp_3885_, lean_object* v_body_3886_, lean_object* v_x_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
uint8_t v_usedLetOnly_boxed_3894_; uint8_t v_skipConstInApp_boxed_3895_; uint8_t v_skipInstances_boxed_3896_; lean_object* v_res_3897_; 
v_usedLetOnly_boxed_3894_ = lean_unbox(v_usedLetOnly_3882_);
v_skipConstInApp_boxed_3895_ = lean_unbox(v_skipConstInApp_3883_);
v_skipInstances_boxed_3896_ = lean_unbox(v_skipInstances_3884_);
v_res_3897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3879_, v_pre_3880_, v_post_3881_, v_usedLetOnly_boxed_3894_, v_skipConstInApp_boxed_3895_, v_skipInstances_boxed_3896_, v_postApp_3885_, v_body_3886_, v_x_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3898_, lean_object* v_pre_3899_, lean_object* v_post_3900_, uint8_t v_usedLetOnly_3901_, uint8_t v_skipConstInApp_3902_, uint8_t v_skipInstances_3903_, lean_object* v_postApp_3904_, lean_object* v_body_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_array_push(v_fvars_3898_, v_x_3906_);
v___x_3914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3899_, v_post_3900_, v_usedLetOnly_3901_, v_skipConstInApp_3902_, v_skipInstances_3903_, v_postApp_3904_, v___x_3913_, v_body_3905_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3915_, lean_object* v_pre_3916_, lean_object* v_post_3917_, lean_object* v_usedLetOnly_3918_, lean_object* v_skipConstInApp_3919_, lean_object* v_skipInstances_3920_, lean_object* v_postApp_3921_, lean_object* v_body_3922_, lean_object* v_x_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v_usedLetOnly_boxed_3930_; uint8_t v_skipConstInApp_boxed_3931_; uint8_t v_skipInstances_boxed_3932_; lean_object* v_res_3933_; 
v_usedLetOnly_boxed_3930_ = lean_unbox(v_usedLetOnly_3918_);
v_skipConstInApp_boxed_3931_ = lean_unbox(v_skipConstInApp_3919_);
v_skipInstances_boxed_3932_ = lean_unbox(v_skipInstances_3920_);
v_res_3933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3915_, v_pre_3916_, v_post_3917_, v_usedLetOnly_boxed_3930_, v_skipConstInApp_boxed_3931_, v_skipInstances_boxed_3932_, v_postApp_3921_, v_body_3922_, v_x_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3934_, lean_object* v_post_3935_, uint8_t v_usedLetOnly_3936_, uint8_t v_skipConstInApp_3937_, uint8_t v_skipInstances_3938_, lean_object* v_postApp_3939_, lean_object* v_e_3940_, lean_object* v_a_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
lean_inc_ref(v_post_3935_);
lean_inc(v___y_3945_);
lean_inc_ref(v___y_3944_);
lean_inc(v___y_3943_);
lean_inc_ref(v___y_3942_);
lean_inc_ref(v_e_3940_);
v___x_3947_ = lean_apply_6(v_post_3935_, v_e_3940_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, lean_box(0));
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3966_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3950_ = v___x_3947_;
v_isShared_3951_ = v_isSharedCheck_3966_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3947_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3966_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
switch(lean_obj_tag(v_a_3948_))
{
case 0:
{
lean_object* v_e_3952_; lean_object* v___x_3954_; 
lean_dec_ref(v_e_3940_);
lean_dec_ref(v_postApp_3939_);
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
v_e_3952_ = lean_ctor_get(v_a_3948_, 0);
lean_inc_ref(v_e_3952_);
lean_dec_ref_known(v_a_3948_, 1);
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v_e_3952_);
v___x_3954_ = v___x_3950_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_e_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
case 1:
{
lean_object* v_e_3956_; lean_object* v___x_3957_; 
lean_del_object(v___x_3950_);
lean_dec_ref(v_e_3940_);
v_e_3956_ = lean_ctor_get(v_a_3948_, 0);
lean_inc_ref(v_e_3956_);
lean_dec_ref_known(v_a_3948_, 1);
v___x_3957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3934_, v_post_3935_, v_usedLetOnly_3936_, v_skipConstInApp_3937_, v_skipInstances_3938_, v_postApp_3939_, v_e_3956_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3957_;
}
default: 
{
lean_object* v_e_x3f_3958_; 
lean_dec_ref(v_postApp_3939_);
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
v_e_x3f_3958_ = lean_ctor_get(v_a_3948_, 0);
lean_inc(v_e_x3f_3958_);
lean_dec_ref_known(v_a_3948_, 1);
if (lean_obj_tag(v_e_x3f_3958_) == 0)
{
lean_object* v___x_3960_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v_e_3940_);
v___x_3960_ = v___x_3950_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_e_3940_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
else
{
lean_object* v_val_3962_; lean_object* v___x_3964_; 
lean_dec_ref(v_e_3940_);
v_val_3962_ = lean_ctor_get(v_e_x3f_3958_, 0);
lean_inc(v_val_3962_);
lean_dec_ref_known(v_e_x3f_3958_, 1);
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v_val_3962_);
v___x_3964_ = v___x_3950_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_val_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v_e_3940_);
lean_dec_ref(v_postApp_3939_);
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
v_a_3967_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3947_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3947_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3975_, lean_object* v_post_3976_, uint8_t v_usedLetOnly_3977_, uint8_t v_skipConstInApp_3978_, uint8_t v_skipInstances_3979_, lean_object* v_postApp_3980_, lean_object* v_fvars_3981_, lean_object* v_e_3982_, lean_object* v_a_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
if (lean_obj_tag(v_e_3982_) == 6)
{
lean_object* v_binderName_3989_; lean_object* v_binderType_3990_; lean_object* v_body_3991_; uint8_t v_binderInfo_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_binderName_3989_ = lean_ctor_get(v_e_3982_, 0);
lean_inc(v_binderName_3989_);
v_binderType_3990_ = lean_ctor_get(v_e_3982_, 1);
lean_inc_ref(v_binderType_3990_);
v_body_3991_ = lean_ctor_get(v_e_3982_, 2);
lean_inc_ref(v_body_3991_);
v_binderInfo_3992_ = lean_ctor_get_uint8(v_e_3982_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3982_, 3);
v___x_3993_ = lean_box(v_usedLetOnly_3977_);
v___x_3994_ = lean_box(v_skipConstInApp_3978_);
v___x_3995_ = lean_box(v_skipInstances_3979_);
lean_inc_ref(v_postApp_3980_);
lean_inc_ref(v_post_3976_);
lean_inc_ref(v_pre_3975_);
lean_inc_ref(v_fvars_3981_);
v___f_3996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3996_, 0, v_fvars_3981_);
lean_closure_set(v___f_3996_, 1, v_pre_3975_);
lean_closure_set(v___f_3996_, 2, v_post_3976_);
lean_closure_set(v___f_3996_, 3, v___x_3993_);
lean_closure_set(v___f_3996_, 4, v___x_3994_);
lean_closure_set(v___f_3996_, 5, v___x_3995_);
lean_closure_set(v___f_3996_, 6, v_postApp_3980_);
lean_closure_set(v___f_3996_, 7, v_body_3991_);
v___x_3997_ = lean_expr_instantiate_rev(v_binderType_3990_, v_fvars_3981_);
lean_dec_ref(v_fvars_3981_);
lean_dec_ref(v_binderType_3990_);
v___x_3998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3975_, v_post_3976_, v_usedLetOnly_3977_, v_skipConstInApp_3978_, v_skipInstances_3979_, v_postApp_3980_, v___x_3997_, v_a_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = 0;
v___x_4001_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3989_, v_binderInfo_3992_, v_a_3999_, v___f_3996_, v___x_4000_, v_a_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_4001_;
}
else
{
lean_dec_ref(v___f_3996_);
lean_dec(v_binderName_3989_);
return v___x_3998_;
}
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_expr_instantiate_rev(v_e_3982_, v_fvars_3981_);
lean_dec_ref(v_e_3982_);
lean_inc_ref(v_postApp_3980_);
lean_inc_ref(v_post_3976_);
lean_inc_ref(v_pre_3975_);
v___x_4003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3975_, v_post_3976_, v_usedLetOnly_3977_, v_skipConstInApp_3978_, v_skipInstances_3979_, v_postApp_3980_, v___x_4002_, v_a_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; uint8_t v___x_4005_; uint8_t v___x_4006_; uint8_t v___x_4007_; lean_object* v___x_4008_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = 0;
v___x_4006_ = 1;
v___x_4007_ = 1;
v___x_4008_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3981_, v_a_4004_, v___x_4005_, v_usedLetOnly_3977_, v___x_4005_, v___x_4006_, v___x_4007_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec_ref(v_fvars_3981_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3975_, v_post_3976_, v_usedLetOnly_3977_, v_skipConstInApp_3978_, v_skipInstances_3979_, v_postApp_3980_, v_a_4009_, v_a_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_4010_;
}
else
{
lean_dec_ref(v_postApp_3980_);
lean_dec_ref(v_post_3976_);
lean_dec_ref(v_pre_3975_);
return v___x_4008_;
}
}
else
{
lean_dec_ref(v_fvars_3981_);
lean_dec_ref(v_postApp_3980_);
lean_dec_ref(v_post_3976_);
lean_dec_ref(v_pre_3975_);
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_4011_, lean_object* v_pre_4012_, lean_object* v_post_4013_, uint8_t v_usedLetOnly_4014_, uint8_t v_skipConstInApp_4015_, uint8_t v_skipInstances_4016_, lean_object* v_postApp_4017_, lean_object* v_body_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_array_push(v_fvars_4011_, v_x_4019_);
v___x_4027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4012_, v_post_4013_, v_usedLetOnly_4014_, v_skipConstInApp_4015_, v_skipInstances_4016_, v_postApp_4017_, v___x_4026_, v_body_4018_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_4028_, lean_object* v_pre_4029_, lean_object* v_post_4030_, lean_object* v_usedLetOnly_4031_, lean_object* v_skipConstInApp_4032_, lean_object* v_skipInstances_4033_, lean_object* v_postApp_4034_, lean_object* v_body_4035_, lean_object* v_x_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
uint8_t v_usedLetOnly_boxed_4043_; uint8_t v_skipConstInApp_boxed_4044_; uint8_t v_skipInstances_boxed_4045_; lean_object* v_res_4046_; 
v_usedLetOnly_boxed_4043_ = lean_unbox(v_usedLetOnly_4031_);
v_skipConstInApp_boxed_4044_ = lean_unbox(v_skipConstInApp_4032_);
v_skipInstances_boxed_4045_ = lean_unbox(v_skipInstances_4033_);
v_res_4046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_4028_, v_pre_4029_, v_post_4030_, v_usedLetOnly_boxed_4043_, v_skipConstInApp_boxed_4044_, v_skipInstances_boxed_4045_, v_postApp_4034_, v_body_4035_, v_x_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_4047_, lean_object* v_post_4048_, uint8_t v_usedLetOnly_4049_, uint8_t v_skipConstInApp_4050_, uint8_t v_skipInstances_4051_, lean_object* v_postApp_4052_, lean_object* v_fvars_4053_, lean_object* v_e_4054_, lean_object* v_a_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
if (lean_obj_tag(v_e_4054_) == 8)
{
lean_object* v_declName_4061_; lean_object* v_type_4062_; lean_object* v_value_4063_; lean_object* v_body_4064_; uint8_t v_nondep_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___f_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_declName_4061_ = lean_ctor_get(v_e_4054_, 0);
lean_inc(v_declName_4061_);
v_type_4062_ = lean_ctor_get(v_e_4054_, 1);
lean_inc_ref(v_type_4062_);
v_value_4063_ = lean_ctor_get(v_e_4054_, 2);
lean_inc_ref(v_value_4063_);
v_body_4064_ = lean_ctor_get(v_e_4054_, 3);
lean_inc_ref(v_body_4064_);
v_nondep_4065_ = lean_ctor_get_uint8(v_e_4054_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4054_, 4);
v___x_4066_ = lean_box(v_usedLetOnly_4049_);
v___x_4067_ = lean_box(v_skipConstInApp_4050_);
v___x_4068_ = lean_box(v_skipInstances_4051_);
lean_inc_ref_n(v_postApp_4052_, 2);
lean_inc_ref_n(v_post_4048_, 2);
lean_inc_ref_n(v_pre_4047_, 2);
lean_inc_ref(v_fvars_4053_);
v___f_4069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4069_, 0, v_fvars_4053_);
lean_closure_set(v___f_4069_, 1, v_pre_4047_);
lean_closure_set(v___f_4069_, 2, v_post_4048_);
lean_closure_set(v___f_4069_, 3, v___x_4066_);
lean_closure_set(v___f_4069_, 4, v___x_4067_);
lean_closure_set(v___f_4069_, 5, v___x_4068_);
lean_closure_set(v___f_4069_, 6, v_postApp_4052_);
lean_closure_set(v___f_4069_, 7, v_body_4064_);
v___x_4070_ = lean_expr_instantiate_rev(v_type_4062_, v_fvars_4053_);
lean_dec_ref(v_type_4062_);
v___x_4071_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4047_, v_post_4048_, v_usedLetOnly_4049_, v_skipConstInApp_4050_, v_skipInstances_4051_, v_postApp_4052_, v___x_4070_, v_a_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = lean_expr_instantiate_rev(v_value_4063_, v_fvars_4053_);
lean_dec_ref(v_fvars_4053_);
lean_dec_ref(v_value_4063_);
v___x_4074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4047_, v_post_4048_, v_usedLetOnly_4049_, v_skipConstInApp_4050_, v_skipInstances_4051_, v_postApp_4052_, v___x_4073_, v_a_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4076_ = 0;
v___x_4077_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_4061_, v_a_4072_, v_a_4075_, v___f_4069_, v_nondep_4065_, v___x_4076_, v_a_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4077_;
}
else
{
lean_dec(v_a_4072_);
lean_dec_ref(v___f_4069_);
lean_dec(v_declName_4061_);
return v___x_4074_;
}
}
else
{
lean_dec_ref(v___f_4069_);
lean_dec_ref(v_value_4063_);
lean_dec(v_declName_4061_);
lean_dec_ref(v_fvars_4053_);
lean_dec_ref(v_postApp_4052_);
lean_dec_ref(v_post_4048_);
lean_dec_ref(v_pre_4047_);
return v___x_4071_;
}
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_expr_instantiate_rev(v_e_4054_, v_fvars_4053_);
lean_dec_ref(v_e_4054_);
lean_inc_ref(v_postApp_4052_);
lean_inc_ref(v_post_4048_);
lean_inc_ref(v_pre_4047_);
v___x_4079_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4047_, v_post_4048_, v_usedLetOnly_4049_, v_skipConstInApp_4050_, v_skipInstances_4051_, v_postApp_4052_, v___x_4078_, v_a_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; uint8_t v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = 0;
v___x_4082_ = 1;
v___x_4083_ = l_Lean_Meta_mkLetFVars(v_fvars_4053_, v_a_4080_, v_usedLetOnly_4049_, v___x_4081_, v___x_4082_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v_fvars_4053_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4047_, v_post_4048_, v_usedLetOnly_4049_, v_skipConstInApp_4050_, v_skipInstances_4051_, v_postApp_4052_, v_a_4084_, v_a_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4085_;
}
else
{
lean_dec_ref(v_postApp_4052_);
lean_dec_ref(v_post_4048_);
lean_dec_ref(v_pre_4047_);
return v___x_4083_;
}
}
else
{
lean_dec_ref(v_fvars_4053_);
lean_dec_ref(v_postApp_4052_);
lean_dec_ref(v_post_4048_);
lean_dec_ref(v_pre_4047_);
return v___x_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_4086_, lean_object* v_post_4087_, uint8_t v_usedLetOnly_4088_, uint8_t v_skipConstInApp_4089_, uint8_t v_skipInstances_4090_, lean_object* v_postApp_4091_, size_t v_sz_4092_, size_t v_i_4093_, lean_object* v_bs_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
uint8_t v___x_4101_; 
v___x_4101_ = lean_usize_dec_lt(v_i_4093_, v_sz_4092_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; 
lean_dec_ref(v_postApp_4091_);
lean_dec_ref(v_post_4087_);
lean_dec_ref(v_pre_4086_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_bs_4094_);
return v___x_4102_;
}
else
{
lean_object* v_v_4103_; lean_object* v___x_4104_; lean_object* v_bs_x27_4105_; lean_object* v___x_4106_; 
v_v_4103_ = lean_array_uget(v_bs_4094_, v_i_4093_);
v___x_4104_ = lean_unsigned_to_nat(0u);
v_bs_x27_4105_ = lean_array_uset(v_bs_4094_, v_i_4093_, v___x_4104_);
lean_inc_ref(v_postApp_4091_);
lean_inc_ref(v_post_4087_);
lean_inc_ref(v_pre_4086_);
v___x_4106_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4086_, v_post_4087_, v_usedLetOnly_4088_, v_skipConstInApp_4089_, v_skipInstances_4090_, v_postApp_4091_, v_v_4103_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = ((size_t)1ULL);
v___x_4109_ = lean_usize_add(v_i_4093_, v___x_4108_);
v___x_4110_ = lean_array_uset(v_bs_x27_4105_, v_i_4093_, v_a_4107_);
v_i_4093_ = v___x_4109_;
v_bs_4094_ = v___x_4110_;
goto _start;
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec_ref(v_bs_x27_4105_);
lean_dec_ref(v_postApp_4091_);
lean_dec_ref(v_post_4087_);
lean_dec_ref(v_pre_4086_);
v_a_4112_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4106_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4106_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4120_, lean_object* v_post_4121_, uint8_t v_usedLetOnly_4122_, uint8_t v_skipConstInApp_4123_, uint8_t v_skipInstances_4124_, lean_object* v_postApp_4125_, lean_object* v___x_4126_, lean_object* v___y_4127_, lean_object* v_b_4128_, lean_object* v_a_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4124_, v_postApp_4125_, v___x_4126_, v___y_4127_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4145_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4140_ = lean_array_fset(v_b_4128_, v_a_4129_, v_a_4136_);
v___x_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4141_);
v___x_4143_ = v___x_4138_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v_b_4128_);
v_a_4146_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4135_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4135_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4154_, lean_object* v_post_4155_, lean_object* v_usedLetOnly_4156_, lean_object* v_skipConstInApp_4157_, lean_object* v_skipInstances_4158_, lean_object* v_postApp_4159_, lean_object* v___x_4160_, lean_object* v___y_4161_, lean_object* v_b_4162_, lean_object* v_a_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
uint8_t v_usedLetOnly_boxed_4169_; uint8_t v_skipConstInApp_boxed_4170_; uint8_t v_skipInstances_boxed_4171_; lean_object* v_res_4172_; 
v_usedLetOnly_boxed_4169_ = lean_unbox(v_usedLetOnly_4156_);
v_skipConstInApp_boxed_4170_ = lean_unbox(v_skipConstInApp_4157_);
v_skipInstances_boxed_4171_ = lean_unbox(v_skipInstances_4158_);
v_res_4172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4154_, v_post_4155_, v_usedLetOnly_boxed_4169_, v_skipConstInApp_boxed_4170_, v_skipInstances_boxed_4171_, v_postApp_4159_, v___x_4160_, v___y_4161_, v_b_4162_, v_a_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v_a_4163_);
lean_dec(v___y_4161_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4173_, lean_object* v___x_4174_, lean_object* v_pre_4175_, lean_object* v_post_4176_, uint8_t v_usedLetOnly_4177_, uint8_t v_skipConstInApp_4178_, uint8_t v_skipInstances_4179_, lean_object* v_postApp_4180_, lean_object* v_a_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___y_4190_; uint8_t v___x_4213_; 
v___x_4213_ = lean_nat_dec_lt(v_a_4181_, v_upperBound_4173_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; 
lean_dec(v_a_4181_);
lean_dec_ref(v_postApp_4180_);
lean_dec_ref(v_post_4176_);
lean_dec_ref(v_pre_4175_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_b_4182_);
return v___x_4214_;
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; 
v___x_4215_ = lean_array_fget_borrowed(v_b_4182_, v_a_4181_);
v___x_4216_ = lean_array_get_size(v___x_4174_);
v___x_4217_ = lean_nat_dec_lt(v_a_4181_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___f_4221_; 
lean_inc(v___x_4215_);
v___x_4218_ = lean_box(v_usedLetOnly_4177_);
v___x_4219_ = lean_box(v_skipConstInApp_4178_);
v___x_4220_ = lean_box(v_skipInstances_4179_);
lean_inc(v_a_4181_);
lean_inc(v___y_4183_);
lean_inc_ref(v_postApp_4180_);
lean_inc_ref(v_post_4176_);
lean_inc_ref(v_pre_4175_);
v___f_4221_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_4221_, 0, v_pre_4175_);
lean_closure_set(v___f_4221_, 1, v_post_4176_);
lean_closure_set(v___f_4221_, 2, v___x_4218_);
lean_closure_set(v___f_4221_, 3, v___x_4219_);
lean_closure_set(v___f_4221_, 4, v___x_4220_);
lean_closure_set(v___f_4221_, 5, v_postApp_4180_);
lean_closure_set(v___f_4221_, 6, v___x_4215_);
lean_closure_set(v___f_4221_, 7, v___y_4183_);
lean_closure_set(v___f_4221_, 8, v_b_4182_);
lean_closure_set(v___f_4221_, 9, v_a_4181_);
v___y_4190_ = v___f_4221_;
goto v___jp_4189_;
}
else
{
lean_object* v___x_4222_; uint8_t v_isInstance_4223_; 
v___x_4222_ = lean_array_fget_borrowed(v___x_4174_, v_a_4181_);
v_isInstance_4223_ = lean_ctor_get_uint8(v___x_4222_, sizeof(void*)*1 + 4);
if (v_isInstance_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___f_4227_; 
lean_inc(v___x_4215_);
v___x_4224_ = lean_box(v_usedLetOnly_4177_);
v___x_4225_ = lean_box(v_skipConstInApp_4178_);
v___x_4226_ = lean_box(v_skipInstances_4179_);
lean_inc(v_a_4181_);
lean_inc(v___y_4183_);
lean_inc_ref(v_postApp_4180_);
lean_inc_ref(v_post_4176_);
lean_inc_ref(v_pre_4175_);
v___f_4227_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_4227_, 0, v_pre_4175_);
lean_closure_set(v___f_4227_, 1, v_post_4176_);
lean_closure_set(v___f_4227_, 2, v___x_4224_);
lean_closure_set(v___f_4227_, 3, v___x_4225_);
lean_closure_set(v___f_4227_, 4, v___x_4226_);
lean_closure_set(v___f_4227_, 5, v_postApp_4180_);
lean_closure_set(v___f_4227_, 6, v___x_4215_);
lean_closure_set(v___f_4227_, 7, v___y_4183_);
lean_closure_set(v___f_4227_, 8, v_b_4182_);
lean_closure_set(v___f_4227_, 9, v_a_4181_);
v___y_4190_ = v___f_4227_;
goto v___jp_4189_;
}
else
{
lean_object* v___x_4228_; lean_object* v___f_4229_; 
v___x_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_b_4182_);
v___f_4229_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4229_, 0, v___x_4228_);
v___y_4190_ = v___f_4229_;
goto v___jp_4189_;
}
}
}
v___jp_4189_:
{
lean_object* v___x_4191_; 
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
v___x_4191_ = lean_apply_5(v___y_4190_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, lean_box(0));
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4204_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4204_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4204_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
if (lean_obj_tag(v_a_4192_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; 
lean_dec(v_a_4181_);
lean_dec_ref(v_postApp_4180_);
lean_dec_ref(v_post_4176_);
lean_dec_ref(v_pre_4175_);
v_a_4196_ = lean_ctor_get(v_a_4192_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v_a_4192_, 1);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v_a_4196_);
v___x_4198_ = v___x_4194_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_del_object(v___x_4194_);
v_a_4200_ = lean_ctor_get(v_a_4192_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v_a_4192_, 1);
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = lean_nat_add(v_a_4181_, v___x_4201_);
lean_dec(v_a_4181_);
v_a_4181_ = v___x_4202_;
v_b_4182_ = v_a_4200_;
goto _start;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec(v_a_4181_);
lean_dec_ref(v_postApp_4180_);
lean_dec_ref(v_post_4176_);
lean_dec_ref(v_pre_4175_);
v_a_4205_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4191_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4191_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4230_, lean_object* v_pre_4231_, lean_object* v_post_4232_, uint8_t v_usedLetOnly_4233_, uint8_t v_skipConstInApp_4234_, lean_object* v_postApp_4235_, lean_object* v___y_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_f_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; 
if (lean_obj_tag(v_x_4237_) == 5)
{
lean_object* v_fn_4299_; lean_object* v_arg_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v_fn_4299_ = lean_ctor_get(v_x_4237_, 0);
lean_inc_ref(v_fn_4299_);
v_arg_4300_ = lean_ctor_get(v_x_4237_, 1);
lean_inc_ref(v_arg_4300_);
lean_dec_ref_known(v_x_4237_, 2);
v___x_4301_ = lean_array_set(v_x_4238_, v_x_4239_, v_arg_4300_);
v___x_4302_ = lean_unsigned_to_nat(1u);
v___x_4303_ = lean_nat_sub(v_x_4239_, v___x_4302_);
lean_dec(v_x_4239_);
v_x_4237_ = v_fn_4299_;
v_x_4238_ = v___x_4301_;
v_x_4239_ = v___x_4303_;
goto _start;
}
else
{
lean_dec(v_x_4239_);
if (v_skipConstInApp_4234_ == 0)
{
goto v___jp_4296_;
}
else
{
uint8_t v___x_4305_; 
v___x_4305_ = l_Lean_Expr_isConst(v_x_4237_);
if (v___x_4305_ == 0)
{
goto v___jp_4296_;
}
else
{
v_f_4247_ = v_x_4237_;
v___y_4248_ = v___y_4240_;
v___y_4249_ = v___y_4241_;
v___y_4250_ = v___y_4242_;
v___y_4251_ = v___y_4243_;
v___y_4252_ = v___y_4244_;
goto v___jp_4246_;
}
}
}
v___jp_4246_:
{
if (v_skipInstances_4230_ == 0)
{
size_t v_sz_4253_; size_t v___x_4254_; lean_object* v___x_4255_; 
v_sz_4253_ = lean_array_size(v_x_4238_);
v___x_4254_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_4235_);
lean_inc_ref(v_post_4232_);
lean_inc_ref(v_pre_4231_);
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4231_, v_post_4232_, v_usedLetOnly_4233_, v_skipConstInApp_4234_, v_skipInstances_4230_, v_postApp_4235_, v_sz_4253_, v___x_4254_, v_x_4238_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = l_Lean_mkAppN(v_f_4247_, v_a_4256_);
lean_dec(v_a_4256_);
lean_inc_ref(v_postApp_4235_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
v___x_4258_ = lean_apply_7(v_postApp_4235_, v___y_4236_, v___x_4257_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, lean_box(0));
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___x_4260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4231_, v_post_4232_, v_usedLetOnly_4233_, v_skipConstInApp_4234_, v_skipInstances_4230_, v_postApp_4235_, v_a_4259_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
return v___x_4260_;
}
else
{
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
return v___x_4258_;
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_f_4247_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
v_a_4261_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4255_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4255_);
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
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = lean_array_get_size(v_x_4238_);
lean_inc_ref(v_f_4247_);
v___x_4270_ = l_Lean_Meta_getFunInfoNArgs(v_f_4247_, v___x_4269_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v_paramInfo_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4270_, 1);
v_paramInfo_4272_ = lean_ctor_get(v_a_4271_, 0);
lean_inc_ref(v_paramInfo_4272_);
lean_dec(v_a_4271_);
v___x_4273_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_4235_);
lean_inc_ref(v_post_4232_);
lean_inc_ref(v_pre_4231_);
v___x_4274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4269_, v_paramInfo_4272_, v_pre_4231_, v_post_4232_, v_usedLetOnly_4233_, v_skipConstInApp_4234_, v_skipInstances_4230_, v_postApp_4235_, v___x_4273_, v_x_4238_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec_ref(v_paramInfo_4272_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v___x_4276_ = l_Lean_mkAppN(v_f_4247_, v_a_4275_);
lean_dec(v_a_4275_);
lean_inc_ref(v_postApp_4235_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
v___x_4277_ = lean_apply_7(v_postApp_4235_, v___y_4236_, v___x_4276_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, lean_box(0));
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v___x_4279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4231_, v_post_4232_, v_usedLetOnly_4233_, v_skipConstInApp_4234_, v_skipInstances_4230_, v_postApp_4235_, v_a_4278_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
return v___x_4279_;
}
else
{
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
return v___x_4277_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v_f_4247_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
v_a_4280_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4274_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4274_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_f_4247_);
lean_dec_ref(v_x_4238_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
v_a_4288_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4270_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4270_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
v___jp_4296_:
{
lean_object* v___x_4297_; 
lean_inc_ref(v_postApp_4235_);
lean_inc_ref(v_post_4232_);
lean_inc_ref(v_pre_4231_);
v___x_4297_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4231_, v_post_4232_, v_usedLetOnly_4233_, v_skipConstInApp_4234_, v_skipInstances_4230_, v_postApp_4235_, v_x_4237_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v_f_4247_ = v_a_4298_;
v___y_4248_ = v___y_4240_;
v___y_4249_ = v___y_4241_;
v___y_4250_ = v___y_4242_;
v___y_4251_ = v___y_4243_;
v___y_4252_ = v___y_4244_;
goto v___jp_4246_;
}
else
{
lean_dec_ref(v_x_4238_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_postApp_4235_);
lean_dec_ref(v_post_4232_);
lean_dec_ref(v_pre_4231_);
return v___x_4297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4306_, lean_object* v_pre_4307_, lean_object* v_e_4308_, lean_object* v_post_4309_, uint8_t v_usedLetOnly_4310_, uint8_t v_skipConstInApp_4311_, uint8_t v_skipInstances_4312_, lean_object* v_postApp_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_Core_checkSystem(v___x_4306_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4321_; 
lean_dec_ref_known(v___x_4320_, 1);
lean_inc_ref(v_pre_4307_);
lean_inc(v___y_4318_);
lean_inc_ref(v___y_4317_);
lean_inc(v___y_4316_);
lean_inc_ref(v___y_4315_);
lean_inc_ref(v_e_4308_);
v___x_4321_ = lean_apply_6(v_pre_4307_, v_e_4308_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, lean_box(0));
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4370_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___y_4327_; 
switch(lean_obj_tag(v_a_4322_))
{
case 0:
{
lean_object* v_e_4362_; lean_object* v___x_4364_; 
lean_dec_ref(v_postApp_4313_);
lean_dec_ref(v_post_4309_);
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_pre_4307_);
v_e_4362_ = lean_ctor_get(v_a_4322_, 0);
lean_inc_ref(v_e_4362_);
lean_dec_ref_known(v_a_4322_, 1);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v_e_4362_);
v___x_4364_ = v___x_4324_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_e_4362_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
case 1:
{
lean_object* v_e_4366_; lean_object* v___x_4367_; 
lean_del_object(v___x_4324_);
lean_dec_ref(v_e_4308_);
v_e_4366_ = lean_ctor_get(v_a_4322_, 0);
lean_inc_ref(v_e_4366_);
lean_dec_ref_known(v_a_4322_, 1);
v___x_4367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v_e_4366_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4367_;
}
default: 
{
lean_object* v_e_x3f_4368_; 
lean_del_object(v___x_4324_);
v_e_x3f_4368_ = lean_ctor_get(v_a_4322_, 0);
lean_inc(v_e_x3f_4368_);
lean_dec_ref_known(v_a_4322_, 1);
if (lean_obj_tag(v_e_x3f_4368_) == 0)
{
v___y_4327_ = v_e_4308_;
goto v___jp_4326_;
}
else
{
lean_object* v_val_4369_; 
lean_dec_ref(v_e_4308_);
v_val_4369_ = lean_ctor_get(v_e_x3f_4368_, 0);
lean_inc(v_val_4369_);
lean_dec_ref_known(v_e_x3f_4368_, 1);
v___y_4327_ = v_val_4369_;
goto v___jp_4326_;
}
}
}
v___jp_4326_:
{
switch(lean_obj_tag(v___y_4327_))
{
case 7:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4328_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___x_4328_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4329_;
}
case 6:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___x_4330_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4331_;
}
case 8:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4333_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___x_4332_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4333_;
}
case 5:
{
lean_object* v_dummy_4334_; lean_object* v_nargs_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v_dummy_4334_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_4335_ = l_Lean_Expr_getAppNumArgs(v___y_4327_);
lean_inc(v_nargs_4335_);
v___x_4336_ = lean_mk_array(v_nargs_4335_, v_dummy_4334_);
v___x_4337_ = lean_unsigned_to_nat(1u);
v___x_4338_ = lean_nat_sub(v_nargs_4335_, v___x_4337_);
lean_dec(v_nargs_4335_);
lean_inc_ref(v___y_4327_);
v___x_4339_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4312_, v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_postApp_4313_, v___y_4327_, v___y_4327_, v___x_4336_, v___x_4338_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4339_;
}
case 10:
{
lean_object* v_data_4340_; lean_object* v_expr_4341_; lean_object* v___x_4342_; 
v_data_4340_ = lean_ctor_get(v___y_4327_, 0);
v_expr_4341_ = lean_ctor_get(v___y_4327_, 1);
lean_inc_ref(v_expr_4341_);
lean_inc_ref(v_postApp_4313_);
lean_inc_ref(v_post_4309_);
lean_inc_ref(v_pre_4307_);
v___x_4342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v_expr_4341_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; size_t v___x_4344_; size_t v___x_4345_; uint8_t v___x_4346_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4342_, 1);
v___x_4344_ = lean_ptr_addr(v_expr_4341_);
v___x_4345_ = lean_ptr_addr(v_a_4343_);
v___x_4346_ = lean_usize_dec_eq(v___x_4344_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
lean_inc(v_data_4340_);
lean_dec_ref_known(v___y_4327_, 2);
v___x_4347_ = l_Lean_Expr_mdata___override(v_data_4340_, v_a_4343_);
v___x_4348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___x_4347_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; 
lean_dec(v_a_4343_);
v___x_4349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4349_;
}
}
else
{
lean_dec_ref_known(v___y_4327_, 2);
lean_dec_ref(v_postApp_4313_);
lean_dec_ref(v_post_4309_);
lean_dec_ref(v_pre_4307_);
return v___x_4342_;
}
}
case 11:
{
lean_object* v_typeName_4350_; lean_object* v_idx_4351_; lean_object* v_struct_4352_; lean_object* v___x_4353_; 
v_typeName_4350_ = lean_ctor_get(v___y_4327_, 0);
v_idx_4351_ = lean_ctor_get(v___y_4327_, 1);
v_struct_4352_ = lean_ctor_get(v___y_4327_, 2);
lean_inc_ref(v_struct_4352_);
lean_inc_ref(v_postApp_4313_);
lean_inc_ref(v_post_4309_);
lean_inc_ref(v_pre_4307_);
v___x_4353_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v_struct_4352_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; size_t v___x_4355_; size_t v___x_4356_; uint8_t v___x_4357_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = lean_ptr_addr(v_struct_4352_);
v___x_4356_ = lean_ptr_addr(v_a_4354_);
v___x_4357_ = lean_usize_dec_eq(v___x_4355_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_inc(v_idx_4351_);
lean_inc(v_typeName_4350_);
lean_dec_ref_known(v___y_4327_, 3);
v___x_4358_ = l_Lean_Expr_proj___override(v_typeName_4350_, v_idx_4351_, v_a_4354_);
v___x_4359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___x_4358_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4359_;
}
else
{
lean_object* v___x_4360_; 
lean_dec(v_a_4354_);
v___x_4360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4360_;
}
}
else
{
lean_dec_ref_known(v___y_4327_, 3);
lean_dec_ref(v_postApp_4313_);
lean_dec_ref(v_post_4309_);
lean_dec_ref(v_pre_4307_);
return v___x_4353_;
}
}
default: 
{
lean_object* v___x_4361_; 
v___x_4361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4307_, v_post_4309_, v_usedLetOnly_4310_, v_skipConstInApp_4311_, v_skipInstances_4312_, v_postApp_4313_, v___y_4327_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4361_;
}
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec_ref(v_postApp_4313_);
lean_dec_ref(v_post_4309_);
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_pre_4307_);
v_a_4371_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4321_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4321_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec_ref(v_postApp_4313_);
lean_dec_ref(v_post_4309_);
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_pre_4307_);
v_a_4379_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4320_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4320_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4387_, lean_object* v_pre_4388_, lean_object* v_e_4389_, lean_object* v_post_4390_, lean_object* v_usedLetOnly_4391_, lean_object* v_skipConstInApp_4392_, lean_object* v_skipInstances_4393_, lean_object* v_postApp_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
uint8_t v_usedLetOnly_boxed_4401_; uint8_t v_skipConstInApp_boxed_4402_; uint8_t v_skipInstances_boxed_4403_; lean_object* v_res_4404_; 
v_usedLetOnly_boxed_4401_ = lean_unbox(v_usedLetOnly_4391_);
v_skipConstInApp_boxed_4402_ = lean_unbox(v_skipConstInApp_4392_);
v_skipInstances_boxed_4403_ = lean_unbox(v_skipInstances_4393_);
v_res_4404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4387_, v_pre_4388_, v_e_4389_, v_post_4390_, v_usedLetOnly_boxed_4401_, v_skipConstInApp_boxed_4402_, v_skipInstances_boxed_4403_, v_postApp_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4405_, lean_object* v_post_4406_, uint8_t v_usedLetOnly_4407_, uint8_t v_skipConstInApp_4408_, uint8_t v_skipInstances_4409_, lean_object* v_postApp_4410_, lean_object* v_e_4411_, lean_object* v_a_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_inc(v_a_4412_);
v___x_4418_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4418_, 0, lean_box(0));
lean_closure_set(v___x_4418_, 1, lean_box(0));
lean_closure_set(v___x_4418_, 2, v_a_4412_);
v___x_4419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4418_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4454_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4454_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4454_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(v_a_4420_, v_e_4411_);
lean_dec(v_a_4420_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; 
lean_del_object(v___x_4422_);
v___x_4425_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0));
v___x_4426_ = lean_box(v_usedLetOnly_4407_);
v___x_4427_ = lean_box(v_skipConstInApp_4408_);
v___x_4428_ = lean_box(v_skipInstances_4409_);
lean_inc_ref(v_e_4411_);
v___f_4429_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4429_, 0, v___x_4425_);
lean_closure_set(v___f_4429_, 1, v_pre_4405_);
lean_closure_set(v___f_4429_, 2, v_e_4411_);
lean_closure_set(v___f_4429_, 3, v_post_4406_);
lean_closure_set(v___f_4429_, 4, v___x_4426_);
lean_closure_set(v___f_4429_, 5, v___x_4427_);
lean_closure_set(v___f_4429_, 6, v___x_4428_);
lean_closure_set(v___f_4429_, 7, v_postApp_4410_);
v___x_4430_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4429_, v_a_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc_n(v_a_4431_, 2);
lean_dec_ref_known(v___x_4430_, 1);
lean_inc(v_a_4412_);
v___f_4432_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4432_, 0, v_a_4412_);
lean_closure_set(v___f_4432_, 1, v_e_4411_);
lean_closure_set(v___f_4432_, 2, v_a_4431_);
v___x_4433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4432_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4440_ == 0)
{
lean_object* v_unused_4441_; 
v_unused_4441_ = lean_ctor_get(v___x_4433_, 0);
lean_dec(v_unused_4441_);
v___x_4435_ = v___x_4433_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_dec(v___x_4433_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v_a_4431_);
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4431_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec(v_a_4431_);
v_a_4442_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4433_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4433_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_dec_ref(v_e_4411_);
return v___x_4430_;
}
}
else
{
lean_object* v_val_4450_; lean_object* v___x_4452_; 
lean_dec_ref(v_e_4411_);
lean_dec_ref(v_postApp_4410_);
lean_dec_ref(v_post_4406_);
lean_dec_ref(v_pre_4405_);
v_val_4450_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_val_4450_);
lean_dec_ref_known(v___x_4424_, 1);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v_val_4450_);
v___x_4452_ = v___x_4422_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_val_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec_ref(v_e_4411_);
lean_dec_ref(v_postApp_4410_);
lean_dec_ref(v_post_4406_);
lean_dec_ref(v_pre_4405_);
v_a_4455_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4419_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4419_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4463_, lean_object* v_post_4464_, uint8_t v_usedLetOnly_4465_, uint8_t v_skipConstInApp_4466_, uint8_t v_skipInstances_4467_, lean_object* v_postApp_4468_, lean_object* v_fvars_4469_, lean_object* v_e_4470_, lean_object* v_a_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
if (lean_obj_tag(v_e_4470_) == 7)
{
lean_object* v_binderName_4477_; lean_object* v_binderType_4478_; lean_object* v_body_4479_; uint8_t v_binderInfo_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___f_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_binderName_4477_ = lean_ctor_get(v_e_4470_, 0);
lean_inc(v_binderName_4477_);
v_binderType_4478_ = lean_ctor_get(v_e_4470_, 1);
lean_inc_ref(v_binderType_4478_);
v_body_4479_ = lean_ctor_get(v_e_4470_, 2);
lean_inc_ref(v_body_4479_);
v_binderInfo_4480_ = lean_ctor_get_uint8(v_e_4470_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4470_, 3);
v___x_4481_ = lean_box(v_usedLetOnly_4465_);
v___x_4482_ = lean_box(v_skipConstInApp_4466_);
v___x_4483_ = lean_box(v_skipInstances_4467_);
lean_inc_ref(v_postApp_4468_);
lean_inc_ref(v_post_4464_);
lean_inc_ref(v_pre_4463_);
lean_inc_ref(v_fvars_4469_);
v___f_4484_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4484_, 0, v_fvars_4469_);
lean_closure_set(v___f_4484_, 1, v_pre_4463_);
lean_closure_set(v___f_4484_, 2, v_post_4464_);
lean_closure_set(v___f_4484_, 3, v___x_4481_);
lean_closure_set(v___f_4484_, 4, v___x_4482_);
lean_closure_set(v___f_4484_, 5, v___x_4483_);
lean_closure_set(v___f_4484_, 6, v_postApp_4468_);
lean_closure_set(v___f_4484_, 7, v_body_4479_);
v___x_4485_ = lean_expr_instantiate_rev(v_binderType_4478_, v_fvars_4469_);
lean_dec_ref(v_fvars_4469_);
lean_dec_ref(v_binderType_4478_);
v___x_4486_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4463_, v_post_4464_, v_usedLetOnly_4465_, v_skipConstInApp_4466_, v_skipInstances_4467_, v_postApp_4468_, v___x_4485_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; uint8_t v___x_4488_; lean_object* v___x_4489_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___x_4488_ = 0;
v___x_4489_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4477_, v_binderInfo_4480_, v_a_4487_, v___f_4484_, v___x_4488_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4489_;
}
else
{
lean_dec_ref(v___f_4484_);
lean_dec(v_binderName_4477_);
return v___x_4486_;
}
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_expr_instantiate_rev(v_e_4470_, v_fvars_4469_);
lean_dec_ref(v_e_4470_);
lean_inc_ref(v_postApp_4468_);
lean_inc_ref(v_post_4464_);
lean_inc_ref(v_pre_4463_);
v___x_4491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4463_, v_post_4464_, v_usedLetOnly_4465_, v_skipConstInApp_4466_, v_skipInstances_4467_, v_postApp_4468_, v___x_4490_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; uint8_t v___x_4493_; uint8_t v___x_4494_; uint8_t v___x_4495_; lean_object* v___x_4496_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = 0;
v___x_4494_ = 1;
v___x_4495_ = 1;
v___x_4496_ = l_Lean_Meta_mkForallFVars(v_fvars_4469_, v_a_4492_, v___x_4493_, v_usedLetOnly_4465_, v___x_4494_, v___x_4495_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec_ref(v_fvars_4469_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4498_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4463_, v_post_4464_, v_usedLetOnly_4465_, v_skipConstInApp_4466_, v_skipInstances_4467_, v_postApp_4468_, v_a_4497_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4498_;
}
else
{
lean_dec_ref(v_postApp_4468_);
lean_dec_ref(v_post_4464_);
lean_dec_ref(v_pre_4463_);
return v___x_4496_;
}
}
else
{
lean_dec_ref(v_fvars_4469_);
lean_dec_ref(v_postApp_4468_);
lean_dec_ref(v_post_4464_);
lean_dec_ref(v_pre_4463_);
return v___x_4491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4499_, lean_object* v_pre_4500_, lean_object* v_post_4501_, uint8_t v_usedLetOnly_4502_, uint8_t v_skipConstInApp_4503_, uint8_t v_skipInstances_4504_, lean_object* v_postApp_4505_, lean_object* v_body_4506_, lean_object* v_x_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_array_push(v_fvars_4499_, v_x_4507_);
v___x_4515_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4500_, v_post_4501_, v_usedLetOnly_4502_, v_skipConstInApp_4503_, v_skipInstances_4504_, v_postApp_4505_, v___x_4514_, v_body_4506_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4516_, lean_object* v_post_4517_, lean_object* v_usedLetOnly_4518_, lean_object* v_skipConstInApp_4519_, lean_object* v_skipInstances_4520_, lean_object* v_postApp_4521_, lean_object* v_e_4522_, lean_object* v_a_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v_usedLetOnly_boxed_4529_; uint8_t v_skipConstInApp_boxed_4530_; uint8_t v_skipInstances_boxed_4531_; lean_object* v_res_4532_; 
v_usedLetOnly_boxed_4529_ = lean_unbox(v_usedLetOnly_4518_);
v_skipConstInApp_boxed_4530_ = lean_unbox(v_skipConstInApp_4519_);
v_skipInstances_boxed_4531_ = lean_unbox(v_skipInstances_4520_);
v_res_4532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4516_, v_post_4517_, v_usedLetOnly_boxed_4529_, v_skipConstInApp_boxed_4530_, v_skipInstances_boxed_4531_, v_postApp_4521_, v_e_4522_, v_a_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v_a_4523_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4533_, lean_object* v_post_4534_, lean_object* v_usedLetOnly_4535_, lean_object* v_skipConstInApp_4536_, lean_object* v_skipInstances_4537_, lean_object* v_postApp_4538_, lean_object* v_sz_4539_, lean_object* v_i_4540_, lean_object* v_bs_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_usedLetOnly_boxed_4548_; uint8_t v_skipConstInApp_boxed_4549_; uint8_t v_skipInstances_boxed_4550_; size_t v_sz_boxed_4551_; size_t v_i_boxed_4552_; lean_object* v_res_4553_; 
v_usedLetOnly_boxed_4548_ = lean_unbox(v_usedLetOnly_4535_);
v_skipConstInApp_boxed_4549_ = lean_unbox(v_skipConstInApp_4536_);
v_skipInstances_boxed_4550_ = lean_unbox(v_skipInstances_4537_);
v_sz_boxed_4551_ = lean_unbox_usize(v_sz_4539_);
lean_dec(v_sz_4539_);
v_i_boxed_4552_ = lean_unbox_usize(v_i_4540_);
lean_dec(v_i_4540_);
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4533_, v_post_4534_, v_usedLetOnly_boxed_4548_, v_skipConstInApp_boxed_4549_, v_skipInstances_boxed_4550_, v_postApp_4538_, v_sz_boxed_4551_, v_i_boxed_4552_, v_bs_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4554_, lean_object* v_post_4555_, lean_object* v_usedLetOnly_4556_, lean_object* v_skipConstInApp_4557_, lean_object* v_skipInstances_4558_, lean_object* v_postApp_4559_, lean_object* v_e_4560_, lean_object* v_a_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
uint8_t v_usedLetOnly_boxed_4567_; uint8_t v_skipConstInApp_boxed_4568_; uint8_t v_skipInstances_boxed_4569_; lean_object* v_res_4570_; 
v_usedLetOnly_boxed_4567_ = lean_unbox(v_usedLetOnly_4556_);
v_skipConstInApp_boxed_4568_ = lean_unbox(v_skipConstInApp_4557_);
v_skipInstances_boxed_4569_ = lean_unbox(v_skipInstances_4558_);
v_res_4570_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4554_, v_post_4555_, v_usedLetOnly_boxed_4567_, v_skipConstInApp_boxed_4568_, v_skipInstances_boxed_4569_, v_postApp_4559_, v_e_4560_, v_a_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v_a_4561_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4571_, lean_object* v_post_4572_, lean_object* v_usedLetOnly_4573_, lean_object* v_skipConstInApp_4574_, lean_object* v_skipInstances_4575_, lean_object* v_postApp_4576_, lean_object* v_fvars_4577_, lean_object* v_e_4578_, lean_object* v_a_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
uint8_t v_usedLetOnly_boxed_4585_; uint8_t v_skipConstInApp_boxed_4586_; uint8_t v_skipInstances_boxed_4587_; lean_object* v_res_4588_; 
v_usedLetOnly_boxed_4585_ = lean_unbox(v_usedLetOnly_4573_);
v_skipConstInApp_boxed_4586_ = lean_unbox(v_skipConstInApp_4574_);
v_skipInstances_boxed_4587_ = lean_unbox(v_skipInstances_4575_);
v_res_4588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4571_, v_post_4572_, v_usedLetOnly_boxed_4585_, v_skipConstInApp_boxed_4586_, v_skipInstances_boxed_4587_, v_postApp_4576_, v_fvars_4577_, v_e_4578_, v_a_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v_a_4579_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4589_, lean_object* v_post_4590_, lean_object* v_usedLetOnly_4591_, lean_object* v_skipConstInApp_4592_, lean_object* v_skipInstances_4593_, lean_object* v_postApp_4594_, lean_object* v_fvars_4595_, lean_object* v_e_4596_, lean_object* v_a_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v_usedLetOnly_boxed_4603_; uint8_t v_skipConstInApp_boxed_4604_; uint8_t v_skipInstances_boxed_4605_; lean_object* v_res_4606_; 
v_usedLetOnly_boxed_4603_ = lean_unbox(v_usedLetOnly_4591_);
v_skipConstInApp_boxed_4604_ = lean_unbox(v_skipConstInApp_4592_);
v_skipInstances_boxed_4605_ = lean_unbox(v_skipInstances_4593_);
v_res_4606_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4589_, v_post_4590_, v_usedLetOnly_boxed_4603_, v_skipConstInApp_boxed_4604_, v_skipInstances_boxed_4605_, v_postApp_4594_, v_fvars_4595_, v_e_4596_, v_a_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v_a_4597_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4607_, lean_object* v_post_4608_, lean_object* v_usedLetOnly_4609_, lean_object* v_skipConstInApp_4610_, lean_object* v_skipInstances_4611_, lean_object* v_postApp_4612_, lean_object* v_fvars_4613_, lean_object* v_e_4614_, lean_object* v_a_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
uint8_t v_usedLetOnly_boxed_4621_; uint8_t v_skipConstInApp_boxed_4622_; uint8_t v_skipInstances_boxed_4623_; lean_object* v_res_4624_; 
v_usedLetOnly_boxed_4621_ = lean_unbox(v_usedLetOnly_4609_);
v_skipConstInApp_boxed_4622_ = lean_unbox(v_skipConstInApp_4610_);
v_skipInstances_boxed_4623_ = lean_unbox(v_skipInstances_4611_);
v_res_4624_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4607_, v_post_4608_, v_usedLetOnly_boxed_4621_, v_skipConstInApp_boxed_4622_, v_skipInstances_boxed_4623_, v_postApp_4612_, v_fvars_4613_, v_e_4614_, v_a_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v_a_4615_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4625_, lean_object* v___x_4626_, lean_object* v_pre_4627_, lean_object* v_post_4628_, lean_object* v_usedLetOnly_4629_, lean_object* v_skipConstInApp_4630_, lean_object* v_skipInstances_4631_, lean_object* v_postApp_4632_, lean_object* v_a_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
uint8_t v_usedLetOnly_boxed_4641_; uint8_t v_skipConstInApp_boxed_4642_; uint8_t v_skipInstances_boxed_4643_; lean_object* v_res_4644_; 
v_usedLetOnly_boxed_4641_ = lean_unbox(v_usedLetOnly_4629_);
v_skipConstInApp_boxed_4642_ = lean_unbox(v_skipConstInApp_4630_);
v_skipInstances_boxed_4643_ = lean_unbox(v_skipInstances_4631_);
v_res_4644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4625_, v___x_4626_, v_pre_4627_, v_post_4628_, v_usedLetOnly_boxed_4641_, v_skipConstInApp_boxed_4642_, v_skipInstances_boxed_4643_, v_postApp_4632_, v_a_4633_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___x_4626_);
lean_dec(v_upperBound_4625_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4645_, lean_object* v_pre_4646_, lean_object* v_post_4647_, lean_object* v_usedLetOnly_4648_, lean_object* v_skipConstInApp_4649_, lean_object* v_postApp_4650_, lean_object* v___y_4651_, lean_object* v_x_4652_, lean_object* v_x_4653_, lean_object* v_x_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
uint8_t v_skipInstances_boxed_4661_; uint8_t v_usedLetOnly_boxed_4662_; uint8_t v_skipConstInApp_boxed_4663_; lean_object* v_res_4664_; 
v_skipInstances_boxed_4661_ = lean_unbox(v_skipInstances_4645_);
v_usedLetOnly_boxed_4662_ = lean_unbox(v_usedLetOnly_4648_);
v_skipConstInApp_boxed_4663_ = lean_unbox(v_skipConstInApp_4649_);
v_res_4664_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4661_, v_pre_4646_, v_post_4647_, v_usedLetOnly_boxed_4662_, v_skipConstInApp_boxed_4663_, v_postApp_4650_, v___y_4651_, v_x_4652_, v_x_4653_, v_x_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1(lean_object* v_x_4665_, lean_object* v_e_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4672_, 0, v_e_4666_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1___boxed(lean_object* v_x_4673_, lean_object* v_e_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1(v_x_4673_, v_e_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec_ref(v_x_4673_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4682_, lean_object* v_pre_4683_, lean_object* v_post_4684_, uint8_t v_usedLetOnly_4685_, uint8_t v_skipConstInApp_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v___f_4692_; uint8_t v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v_a_4696_; lean_object* v___x_4697_; 
v___f_4692_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___closed__0));
v___x_4693_ = 0;
v___x_4694_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4695_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4694_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref(v___x_4695_);
v___x_4697_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4683_, v_post_4684_, v_usedLetOnly_4685_, v_skipConstInApp_4686_, v___x_4693_, v___f_4692_, v_input_4682_, v_a_4696_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v___x_4699_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4699_, 0, lean_box(0));
lean_closure_set(v___x_4699_, 1, lean_box(0));
lean_closure_set(v___x_4699_, 2, v_a_4696_);
v___x_4700_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4699_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; 
v_unused_4708_ = lean_ctor_get(v___x_4700_, 0);
lean_dec(v_unused_4708_);
v___x_4702_ = v___x_4700_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_dec(v___x_4700_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v_a_4698_);
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4698_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
else
{
lean_dec(v_a_4696_);
return v___x_4697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4709_, lean_object* v_pre_4710_, lean_object* v_post_4711_, lean_object* v_usedLetOnly_4712_, lean_object* v_skipConstInApp_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
uint8_t v_usedLetOnly_boxed_4719_; uint8_t v_skipConstInApp_boxed_4720_; lean_object* v_res_4721_; 
v_usedLetOnly_boxed_4719_ = lean_unbox(v_usedLetOnly_4712_);
v_skipConstInApp_boxed_4720_ = lean_unbox(v_skipConstInApp_4713_);
v_res_4721_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4709_, v_pre_4710_, v_post_4711_, v_usedLetOnly_boxed_4719_, v_skipConstInApp_boxed_4720_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4723_, uint8_t v_zetaDelta_4724_, uint8_t v_zetaHave_4725_, uint8_t v_beta_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_lctx_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___f_4736_; uint8_t v___x_4737_; 
v_lctx_4732_ = lean_ctor_get(v_a_4727_, 2);
lean_inc_ref(v_lctx_4732_);
v___x_4733_ = lean_local_ctx_num_indices(v_lctx_4732_);
v___x_4734_ = lean_box(v_zetaHave_4725_);
v___x_4735_ = lean_box(v_zetaDelta_4724_);
v___f_4736_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4736_, 0, v___x_4734_);
lean_closure_set(v___f_4736_, 1, v___x_4733_);
lean_closure_set(v___f_4736_, 2, v___x_4735_);
v___x_4737_ = 1;
if (v_beta_4726_ == 0)
{
lean_object* v___f_4738_; lean_object* v___f_4739_; lean_object* v___x_4740_; 
v___f_4738_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4739_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4739_, 0, v___f_4736_);
v___x_4740_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4723_, v___f_4739_, v___f_4738_, v___x_4737_, v_beta_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
return v___x_4740_;
}
else
{
lean_object* v___f_4741_; lean_object* v___f_4742_; uint8_t v___x_4743_; lean_object* v___x_4744_; 
v___f_4741_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4742_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4742_, 0, v___f_4736_);
v___x_4743_ = 0;
v___x_4744_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4723_, v___f_4742_, v___f_4741_, v___x_4737_, v___x_4743_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
return v___x_4744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4745_, lean_object* v_zetaDelta_4746_, lean_object* v_zetaHave_4747_, lean_object* v_beta_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
uint8_t v_zetaDelta_boxed_4754_; uint8_t v_zetaHave_boxed_4755_; uint8_t v_beta_boxed_4756_; lean_object* v_res_4757_; 
v_zetaDelta_boxed_4754_ = lean_unbox(v_zetaDelta_4746_);
v_zetaHave_boxed_4755_ = lean_unbox(v_zetaHave_4747_);
v_beta_boxed_4756_ = lean_unbox(v_beta_4748_);
v_res_4757_ = l_Lean_Meta_zetaReduce(v_e_4745_, v_zetaDelta_boxed_4754_, v_zetaHave_boxed_4755_, v_beta_boxed_4756_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4758_, lean_object* v___x_4759_, lean_object* v_pre_4760_, lean_object* v_post_4761_, uint8_t v_usedLetOnly_4762_, uint8_t v_skipConstInApp_4763_, uint8_t v_skipInstances_4764_, lean_object* v_postApp_4765_, lean_object* v___x_4766_, lean_object* v_inst_4767_, lean_object* v_R_4768_, lean_object* v_a_4769_, lean_object* v_b_4770_, lean_object* v_c_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4758_, v___x_4759_, v_pre_4760_, v_post_4761_, v_usedLetOnly_4762_, v_skipConstInApp_4763_, v_skipInstances_4764_, v_postApp_4765_, v_a_4769_, v_b_4770_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4779_ = _args[0];
lean_object* v___x_4780_ = _args[1];
lean_object* v_pre_4781_ = _args[2];
lean_object* v_post_4782_ = _args[3];
lean_object* v_usedLetOnly_4783_ = _args[4];
lean_object* v_skipConstInApp_4784_ = _args[5];
lean_object* v_skipInstances_4785_ = _args[6];
lean_object* v_postApp_4786_ = _args[7];
lean_object* v___x_4787_ = _args[8];
lean_object* v_inst_4788_ = _args[9];
lean_object* v_R_4789_ = _args[10];
lean_object* v_a_4790_ = _args[11];
lean_object* v_b_4791_ = _args[12];
lean_object* v_c_4792_ = _args[13];
lean_object* v___y_4793_ = _args[14];
lean_object* v___y_4794_ = _args[15];
lean_object* v___y_4795_ = _args[16];
lean_object* v___y_4796_ = _args[17];
lean_object* v___y_4797_ = _args[18];
lean_object* v___y_4798_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_4799_; uint8_t v_skipConstInApp_boxed_4800_; uint8_t v_skipInstances_boxed_4801_; lean_object* v_res_4802_; 
v_usedLetOnly_boxed_4799_ = lean_unbox(v_usedLetOnly_4783_);
v_skipConstInApp_boxed_4800_ = lean_unbox(v_skipConstInApp_4784_);
v_skipInstances_boxed_4801_ = lean_unbox(v_skipInstances_4785_);
v_res_4802_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4779_, v___x_4780_, v_pre_4781_, v_post_4782_, v_usedLetOnly_boxed_4799_, v_skipConstInApp_boxed_4800_, v_skipInstances_boxed_4801_, v_postApp_4786_, v___x_4787_, v_inst_4788_, v_R_4789_, v_a_4790_, v_b_4791_, v_c_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec(v___x_4787_);
lean_dec_ref(v___x_4780_);
lean_dec(v_upperBound_4779_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4803_, lean_object* v_name_4804_, uint8_t v_bi_4805_, lean_object* v_type_4806_, lean_object* v_k_4807_, uint8_t v_kind_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4804_, v_bi_4805_, v_type_4806_, v_k_4807_, v_kind_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4816_, lean_object* v_name_4817_, lean_object* v_bi_4818_, lean_object* v_type_4819_, lean_object* v_k_4820_, lean_object* v_kind_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
uint8_t v_bi_boxed_4828_; uint8_t v_kind_boxed_4829_; lean_object* v_res_4830_; 
v_bi_boxed_4828_ = lean_unbox(v_bi_4818_);
v_kind_boxed_4829_ = lean_unbox(v_kind_4821_);
v_res_4830_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4816_, v_name_4817_, v_bi_boxed_4828_, v_type_4819_, v_k_4820_, v_kind_boxed_4829_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4831_, lean_object* v_name_4832_, lean_object* v_type_4833_, lean_object* v_val_4834_, lean_object* v_k_4835_, uint8_t v_nondep_4836_, uint8_t v_kind_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4832_, v_type_4833_, v_val_4834_, v_k_4835_, v_nondep_4836_, v_kind_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_name_4846_, lean_object* v_type_4847_, lean_object* v_val_4848_, lean_object* v_k_4849_, lean_object* v_nondep_4850_, lean_object* v_kind_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
uint8_t v_nondep_boxed_4858_; uint8_t v_kind_boxed_4859_; lean_object* v_res_4860_; 
v_nondep_boxed_4858_ = lean_unbox(v_nondep_4850_);
v_kind_boxed_4859_ = lean_unbox(v_kind_4851_);
v_res_4860_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4845_, v_name_4846_, v_type_4847_, v_val_4848_, v_k_4849_, v_nondep_boxed_4858_, v_kind_boxed_4859_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4861_, lean_object* v_ref_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4862_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4869_, lean_object* v_ref_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4869_, v_ref_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4877_, lean_object* v_x_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4886_, lean_object* v_x_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4886_, v_x_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___y_4888_);
return v_res_4894_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4895_, lean_object* v_as_4896_, size_t v_i_4897_, size_t v_stop_4898_){
_start:
{
uint8_t v___x_4899_; 
v___x_4899_ = lean_usize_dec_eq(v_i_4897_, v_stop_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4900_ = lean_array_uget_borrowed(v_as_4896_, v_i_4897_);
v___x_4901_ = l_Lean_instBEqFVarId_beq(v_a_4895_, v___x_4900_);
if (v___x_4901_ == 0)
{
size_t v___x_4902_; size_t v___x_4903_; 
v___x_4902_ = ((size_t)1ULL);
v___x_4903_ = lean_usize_add(v_i_4897_, v___x_4902_);
v_i_4897_ = v___x_4903_;
goto _start;
}
else
{
return v___x_4901_;
}
}
else
{
uint8_t v___x_4905_; 
v___x_4905_ = 0;
return v___x_4905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4906_, lean_object* v_as_4907_, lean_object* v_i_4908_, lean_object* v_stop_4909_){
_start:
{
size_t v_i_boxed_4910_; size_t v_stop_boxed_4911_; uint8_t v_res_4912_; lean_object* v_r_4913_; 
v_i_boxed_4910_ = lean_unbox_usize(v_i_4908_);
lean_dec(v_i_4908_);
v_stop_boxed_4911_ = lean_unbox_usize(v_stop_4909_);
lean_dec(v_stop_4909_);
v_res_4912_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4906_, v_as_4907_, v_i_boxed_4910_, v_stop_boxed_4911_);
lean_dec_ref(v_as_4907_);
lean_dec(v_a_4906_);
v_r_4913_ = lean_box(v_res_4912_);
return v_r_4913_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4914_, lean_object* v_a_4915_){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v___x_4916_ = lean_unsigned_to_nat(0u);
v___x_4917_ = lean_array_get_size(v_as_4914_);
v___x_4918_ = lean_nat_dec_lt(v___x_4916_, v___x_4917_);
if (v___x_4918_ == 0)
{
return v___x_4918_;
}
else
{
size_t v___x_4919_; size_t v___x_4920_; uint8_t v___x_4921_; 
v___x_4919_ = ((size_t)0ULL);
v___x_4920_ = lean_usize_of_nat(v___x_4917_);
v___x_4921_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4915_, v_as_4914_, v___x_4919_, v___x_4920_);
return v___x_4921_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4922_, lean_object* v_a_4923_){
_start:
{
uint8_t v_res_4924_; lean_object* v_r_4925_; 
v_res_4924_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4922_, v_a_4923_);
lean_dec(v_a_4923_);
lean_dec_ref(v_as_4922_);
v_r_4925_ = lean_box(v_res_4924_);
return v_r_4925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4926_, lean_object* v_e_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l_Lean_Expr_getAppFn(v_e_4927_);
if (lean_obj_tag(v___x_4936_) == 1)
{
lean_object* v_fvarId_4937_; uint8_t v___x_4938_; 
v_fvarId_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_fvarId_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4926_, v_fvarId_4937_);
if (v___x_4938_ == 0)
{
lean_dec(v_fvarId_4937_);
lean_dec_ref(v_e_4927_);
goto v___jp_4933_;
}
else
{
uint8_t v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = 0;
v___x_4940_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4937_, v___x_4939_, v___y_4928_, v___y_4930_, v___y_4931_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v___x_4940_, 1);
if (lean_obj_tag(v_a_4941_) == 1)
{
lean_object* v_val_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4965_; 
v_val_4942_ = lean_ctor_get(v_a_4941_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v_a_4941_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4944_ = v_a_4941_;
v_isShared_4945_ = v_isSharedCheck_4965_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_val_4942_);
lean_dec(v_a_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4965_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4946_; lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4964_; 
v___x_4946_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4942_, v___y_4929_);
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4949_ = v___x_4946_;
v_isShared_4950_ = v_isSharedCheck_4964_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4964_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v_dummy_4951_; lean_object* v_nargs_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
v_dummy_4951_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_4952_ = l_Lean_Expr_getAppNumArgs(v_e_4927_);
lean_inc(v_nargs_4952_);
v___x_4953_ = lean_mk_array(v_nargs_4952_, v_dummy_4951_);
v___x_4954_ = lean_unsigned_to_nat(1u);
v___x_4955_ = lean_nat_sub(v_nargs_4952_, v___x_4954_);
lean_dec(v_nargs_4952_);
v___x_4956_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4927_, v___x_4953_, v___x_4955_);
v___x_4957_ = l_Lean_Expr_beta(v_a_4947_, v___x_4956_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4957_);
v___x_4959_ = v___x_4944_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4957_);
v___x_4959_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4961_; 
if (v_isShared_4950_ == 0)
{
lean_ctor_set(v___x_4949_, 0, v___x_4959_);
v___x_4961_ = v___x_4949_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4959_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
else
{
lean_dec(v_a_4941_);
lean_dec_ref(v_e_4927_);
goto v___jp_4933_;
}
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
lean_dec_ref(v_e_4927_);
v_a_4966_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4940_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4940_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
else
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_dec_ref(v___x_4936_);
lean_dec_ref(v_e_4927_);
v___x_4974_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
return v___x_4975_;
}
v___jp_4933_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4976_, lean_object* v_e_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4976_, v_e_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec_ref(v_fvars_4976_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4984_, lean_object* v_fvars_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v___f_4991_; lean_object* v_pre_4992_; uint8_t v___x_4993_; lean_object* v___x_4994_; 
v___f_4991_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4992_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4992_, 0, v_fvars_4985_);
v___x_4993_ = 0;
v___x_4994_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4984_, v_pre_4992_, v___f_4991_, v___x_4993_, v___x_4993_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4995_, lean_object* v_fvars_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_Meta_zetaDeltaFVars(v_e_4995_, v_fvars_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
return v_res_5002_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_5003_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5004_);
return v___x_5005_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5006_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v___x_5011_; lean_object* v_nextMacroScope_5012_; lean_object* v_ngen_5013_; lean_object* v_auxDeclNGen_5014_; lean_object* v_traceState_5015_; lean_object* v_recordedDeps_5016_; lean_object* v_messages_5017_; lean_object* v_infoState_5018_; lean_object* v_snapshotTasks_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5030_; 
v___x_5011_ = lean_st_ref_take(v___y_5009_);
v_nextMacroScope_5012_ = lean_ctor_get(v___x_5011_, 1);
v_ngen_5013_ = lean_ctor_get(v___x_5011_, 2);
v_auxDeclNGen_5014_ = lean_ctor_get(v___x_5011_, 3);
v_traceState_5015_ = lean_ctor_get(v___x_5011_, 4);
v_recordedDeps_5016_ = lean_ctor_get(v___x_5011_, 6);
v_messages_5017_ = lean_ctor_get(v___x_5011_, 7);
v_infoState_5018_ = lean_ctor_get(v___x_5011_, 8);
v_snapshotTasks_5019_ = lean_ctor_get(v___x_5011_, 9);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5030_ == 0)
{
lean_object* v_unused_5031_; lean_object* v_unused_5032_; 
v_unused_5031_ = lean_ctor_get(v___x_5011_, 5);
lean_dec(v_unused_5031_);
v_unused_5032_ = lean_ctor_get(v___x_5011_, 0);
lean_dec(v_unused_5032_);
v___x_5021_ = v___x_5011_;
v_isShared_5022_ = v_isSharedCheck_5030_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_snapshotTasks_5019_);
lean_inc(v_infoState_5018_);
lean_inc(v_messages_5017_);
lean_inc(v_recordedDeps_5016_);
lean_inc(v_traceState_5015_);
lean_inc(v_auxDeclNGen_5014_);
lean_inc(v_ngen_5013_);
lean_inc(v_nextMacroScope_5012_);
lean_dec(v___x_5011_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5030_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5023_ = lean_box(0);
v___x_5024_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 5, v___x_5024_);
lean_ctor_set(v___x_5021_, 0, v_env_5008_);
v___x_5026_ = v___x_5021_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_env_5008_);
lean_ctor_set(v_reuseFailAlloc_5029_, 1, v_nextMacroScope_5012_);
lean_ctor_set(v_reuseFailAlloc_5029_, 2, v_ngen_5013_);
lean_ctor_set(v_reuseFailAlloc_5029_, 3, v_auxDeclNGen_5014_);
lean_ctor_set(v_reuseFailAlloc_5029_, 4, v_traceState_5015_);
lean_ctor_set(v_reuseFailAlloc_5029_, 5, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5029_, 6, v_recordedDeps_5016_);
lean_ctor_set(v_reuseFailAlloc_5029_, 7, v_messages_5017_);
lean_ctor_set(v_reuseFailAlloc_5029_, 8, v_infoState_5018_);
lean_ctor_set(v_reuseFailAlloc_5029_, 9, v_snapshotTasks_5019_);
v___x_5026_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5027_ = lean_st_ref_put(v___y_5009_, v___x_5026_);
v___x_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5028_, 0, v___x_5023_);
return v___x_5028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5033_, v___y_5034_);
lean_dec(v___y_5034_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
lean_object* v___x_5041_; 
v___x_5041_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5037_, v___y_5039_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_5047_, lean_object* v___x_5048_, uint8_t v___x_5049_, lean_object* v_e_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
if (lean_obj_tag(v_e_5050_) == 4)
{
lean_object* v_declName_5054_; lean_object* v_us_5055_; uint8_t v___x_5056_; uint8_t v___x_5057_; 
v_declName_5054_ = lean_ctor_get(v_e_5050_, 0);
v_us_5055_ = lean_ctor_get(v_e_5050_, 1);
v___x_5056_ = 1;
lean_inc(v_declName_5054_);
v___x_5057_ = l_Lean_Environment_contains(v_env_5047_, v_declName_5054_, v___x_5056_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_inc(v_declName_5054_);
v___x_5058_ = l_Lean_Environment_find_x3f(v___x_5048_, v_declName_5054_, v___x_5049_);
if (lean_obj_tag(v___x_5058_) == 1)
{
lean_object* v_val_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5088_; 
v_val_5059_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5061_ = v___x_5058_;
v_isShared_5062_ = v_isSharedCheck_5088_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_val_5059_);
lean_dec(v___x_5058_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5088_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
uint8_t v___x_5063_; 
v___x_5063_ = l_Lean_ConstantInfo_hasValue(v_val_5059_, v___x_5056_);
if (v___x_5063_ == 0)
{
lean_object* v___x_5065_; 
lean_dec(v_val_5059_);
if (v_isShared_5062_ == 0)
{
lean_ctor_set_tag(v___x_5061_, 0);
lean_ctor_set(v___x_5061_, 0, v_e_5050_);
v___x_5065_ = v___x_5061_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_e_5050_);
v___x_5065_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
lean_object* v___x_5066_; 
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
return v___x_5066_;
}
}
else
{
lean_object* v___x_5068_; 
lean_inc(v_us_5055_);
lean_dec_ref_known(v_e_5050_, 2);
v___x_5068_ = l_Lean_Core_instantiateValueLevelParams(v_val_5059_, v_us_5055_, v___x_5056_, v___y_5051_, v___y_5052_);
lean_dec(v_val_5059_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5079_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5071_ = v___x_5068_;
v_isShared_5072_ = v_isSharedCheck_5079_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5079_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 0, v_a_5069_);
v___x_5074_ = v___x_5061_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5076_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v___x_5074_);
v___x_5076_ = v___x_5071_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_del_object(v___x_5061_);
v_a_5080_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5068_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5068_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
}
}
else
{
lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec(v___x_5058_);
v___x_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_e_5050_);
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
return v___x_5090_;
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
lean_dec_ref(v___x_5048_);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v_e_5050_);
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
return v___x_5092_;
}
}
else
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
lean_dec_ref(v_e_5050_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_env_5047_);
v___x_5093_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
return v___x_5094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_5095_, lean_object* v___x_5096_, lean_object* v___x_5097_, lean_object* v_e_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
uint8_t v___x_1999__boxed_5102_; lean_object* v_res_5103_; 
v___x_1999__boxed_5102_ = lean_unbox(v___x_5097_);
v_res_5103_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_5095_, v___x_5096_, v___x_1999__boxed_5102_, v_e_5098_, v___y_5099_, v___y_5100_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_5104_, lean_object* v_e_5105_, lean_object* v___f_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v___x_5110_; lean_object* v_env_5111_; uint8_t v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___f_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5110_ = lean_st_ref_get(v___y_5108_);
v_env_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc_ref(v_env_5111_);
lean_dec(v___x_5110_);
v___x_5112_ = 0;
v___x_5113_ = l_Lean_Environment_setExporting(v_biggerEnv_5104_, v___x_5112_);
v___x_5114_ = lean_box(v___x_5112_);
lean_inc_ref(v___x_5113_);
v___f_5115_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5115_, 0, v_env_5111_);
lean_closure_set(v___f_5115_, 1, v___x_5113_);
lean_closure_set(v___f_5115_, 2, v___x_5114_);
v___x_5116_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_5113_, v___y_5108_);
lean_dec_ref(v___x_5116_);
v___x_5117_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5105_, v___f_5115_, v___f_5106_, v___y_5107_, v___y_5108_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5118_, lean_object* v_e_5119_, lean_object* v___f_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5118_, v_e_5119_, v___f_5120_, v___y_5121_, v___y_5122_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5125_, lean_object* v_x_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_){
_start:
{
lean_object* v___x_5130_; lean_object* v_env_5131_; lean_object* v_a_5133_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5130_ = lean_st_ref_get(v___y_5128_);
v_env_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc_ref(v_env_5131_);
lean_dec(v___x_5130_);
v___x_5143_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5125_, v___y_5128_);
lean_dec_ref(v___x_5143_);
lean_inc(v___y_5128_);
lean_inc_ref(v___y_5127_);
v___x_5144_ = lean_apply_3(v_x_5126_, v___y_5127_, v___y_5128_, lean_box(0));
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5131_, v___y_5128_);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5153_ == 0)
{
lean_object* v_unused_5154_; 
v_unused_5154_ = lean_ctor_get(v___x_5146_, 0);
lean_dec(v_unused_5154_);
v___x_5148_ = v___x_5146_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_dec(v___x_5146_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v_a_5145_);
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5145_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
else
{
lean_object* v_a_5155_; 
v_a_5155_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5144_, 1);
v_a_5133_ = v_a_5155_;
goto v___jp_5132_;
}
v___jp_5132_:
{
lean_object* v___x_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
v___x_5134_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5131_, v___y_5128_);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5141_ == 0)
{
lean_object* v_unused_5142_; 
v_unused_5142_ = lean_ctor_get(v___x_5134_, 0);
lean_dec(v_unused_5142_);
v___x_5136_ = v___x_5134_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_dec(v___x_5134_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
lean_ctor_set_tag(v___x_5136_, 1);
lean_ctor_set(v___x_5136_, 0, v_a_5133_);
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5133_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5156_, lean_object* v_x_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5156_, v_x_5157_, v___y_5158_, v___y_5159_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5162_, lean_object* v_e_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v___f_5167_; lean_object* v___f_5168_; lean_object* v___x_5169_; lean_object* v_env_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___f_5167_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5168_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5168_, 0, v_biggerEnv_5162_);
lean_closure_set(v___f_5168_, 1, v_e_5163_);
lean_closure_set(v___f_5168_, 2, v___f_5167_);
v___x_5169_ = lean_st_ref_get(v_a_5165_);
v_env_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc_ref(v_env_5170_);
lean_dec(v___x_5169_);
v___x_5171_ = l_Lean_Environment_unlockAsync(v_env_5170_);
v___x_5172_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5171_, v___f_5168_, v_a_5164_, v_a_5165_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5173_, lean_object* v_e_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5173_, v_e_5174_, v_a_5175_, v_a_5176_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5179_, lean_object* v_env_5180_, lean_object* v_x_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5180_, v_x_5181_, v___y_5182_, v___y_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5186_, lean_object* v_env_5187_, lean_object* v_x_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5186_, v_env_5187_, v_x_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
return v_res_5192_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5193_, lean_object* v_axs_5194_, lean_object* v_numSectionVars_5195_, lean_object* v_as_5196_, size_t v_i_5197_, size_t v_stop_5198_){
_start:
{
uint8_t v___x_5203_; 
v___x_5203_ = lean_usize_dec_eq(v_i_5197_, v_stop_5198_);
if (v___x_5203_ == 0)
{
lean_object* v___x_5204_; lean_object* v___x_5205_; uint8_t v___x_5206_; 
v___x_5204_ = lean_array_uget_borrowed(v_as_5196_, v_i_5197_);
v___x_5205_ = l_Lean_Expr_constName_x21(v_af_5193_);
v___x_5206_ = lean_name_eq(v___x_5205_, v___x_5204_);
lean_dec(v___x_5205_);
if (v___x_5206_ == 0)
{
goto v___jp_5199_;
}
else
{
lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5207_ = lean_array_get_size(v_axs_5194_);
v___x_5208_ = lean_nat_dec_le(v___x_5207_, v_numSectionVars_5195_);
if (v___x_5208_ == 0)
{
goto v___jp_5199_;
}
else
{
return v___x_5208_;
}
}
}
else
{
uint8_t v___x_5209_; 
v___x_5209_ = 0;
return v___x_5209_;
}
v___jp_5199_:
{
size_t v___x_5200_; size_t v___x_5201_; 
v___x_5200_ = ((size_t)1ULL);
v___x_5201_ = lean_usize_add(v_i_5197_, v___x_5200_);
v_i_5197_ = v___x_5201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5210_, lean_object* v_axs_5211_, lean_object* v_numSectionVars_5212_, lean_object* v_as_5213_, lean_object* v_i_5214_, lean_object* v_stop_5215_){
_start:
{
size_t v_i_boxed_5216_; size_t v_stop_boxed_5217_; uint8_t v_res_5218_; lean_object* v_r_5219_; 
v_i_boxed_5216_ = lean_unbox_usize(v_i_5214_);
lean_dec(v_i_5214_);
v_stop_boxed_5217_ = lean_unbox_usize(v_stop_5215_);
lean_dec(v_stop_5215_);
v_res_5218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5210_, v_axs_5211_, v_numSectionVars_5212_, v_as_5213_, v_i_boxed_5216_, v_stop_boxed_5217_);
lean_dec_ref(v_as_5213_);
lean_dec(v_numSectionVars_5212_);
lean_dec_ref(v_axs_5211_);
lean_dec_ref(v_af_5210_);
v_r_5219_ = lean_box(v_res_5218_);
return v_r_5219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5220_, lean_object* v_numSectionVars_5221_, lean_object* v_x_5222_, lean_object* v_x_5223_, lean_object* v_x_5224_){
_start:
{
if (lean_obj_tag(v_x_5222_) == 5)
{
lean_object* v_fn_5225_; lean_object* v_arg_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_fn_5225_ = lean_ctor_get(v_x_5222_, 0);
lean_inc_ref(v_fn_5225_);
v_arg_5226_ = lean_ctor_get(v_x_5222_, 1);
lean_inc_ref(v_arg_5226_);
lean_dec_ref_known(v_x_5222_, 2);
v___x_5227_ = lean_array_set(v_x_5223_, v_x_5224_, v_arg_5226_);
v___x_5228_ = lean_unsigned_to_nat(1u);
v___x_5229_ = lean_nat_sub(v_x_5224_, v___x_5228_);
lean_dec(v_x_5224_);
v_x_5222_ = v_fn_5225_;
v_x_5223_ = v___x_5227_;
v_x_5224_ = v___x_5229_;
goto _start;
}
else
{
uint8_t v___x_5231_; 
lean_dec(v_x_5224_);
v___x_5231_ = l_Lean_Expr_isConst(v_x_5222_);
if (v___x_5231_ == 0)
{
lean_dec_ref(v_x_5223_);
lean_dec_ref(v_x_5222_);
return v___x_5231_;
}
else
{
lean_object* v___x_5232_; lean_object* v___x_5233_; uint8_t v___x_5234_; 
v___x_5232_ = lean_unsigned_to_nat(0u);
v___x_5233_ = lean_array_get_size(v_fnNames_5220_);
v___x_5234_ = lean_nat_dec_lt(v___x_5232_, v___x_5233_);
if (v___x_5234_ == 0)
{
lean_dec_ref(v_x_5223_);
lean_dec_ref(v_x_5222_);
return v___x_5234_;
}
else
{
if (v___x_5234_ == 0)
{
lean_dec_ref(v_x_5223_);
lean_dec_ref(v_x_5222_);
return v___x_5234_;
}
else
{
size_t v___x_5235_; size_t v___x_5236_; uint8_t v___x_5237_; 
v___x_5235_ = ((size_t)0ULL);
v___x_5236_ = lean_usize_of_nat(v___x_5233_);
v___x_5237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5222_, v_x_5223_, v_numSectionVars_5221_, v_fnNames_5220_, v___x_5235_, v___x_5236_);
lean_dec_ref(v_x_5223_);
lean_dec_ref(v_x_5222_);
return v___x_5237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5238_, lean_object* v_numSectionVars_5239_, lean_object* v_x_5240_, lean_object* v_x_5241_, lean_object* v_x_5242_){
_start:
{
uint8_t v_res_5243_; lean_object* v_r_5244_; 
v_res_5243_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5238_, v_numSectionVars_5239_, v_x_5240_, v_x_5241_, v_x_5242_);
lean_dec(v_numSectionVars_5239_);
lean_dec_ref(v_fnNames_5238_);
v_r_5244_ = lean_box(v_res_5243_);
return v_r_5244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5245_, lean_object* v_fnNames_5246_, lean_object* v_x_5247_, lean_object* v_x_5248_, lean_object* v_x_5249_){
_start:
{
if (lean_obj_tag(v_x_5247_) == 5)
{
lean_object* v_fn_5250_; lean_object* v_arg_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; uint8_t v___x_5255_; 
v_fn_5250_ = lean_ctor_get(v_x_5247_, 0);
lean_inc_ref(v_fn_5250_);
v_arg_5251_ = lean_ctor_get(v_x_5247_, 1);
lean_inc_ref(v_arg_5251_);
lean_dec_ref_known(v_x_5247_, 2);
v___x_5252_ = lean_array_set(v_x_5248_, v_x_5249_, v_arg_5251_);
v___x_5253_ = lean_unsigned_to_nat(1u);
v___x_5254_ = lean_nat_sub(v_x_5249_, v___x_5253_);
v___x_5255_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5246_, v_numSectionVars_5245_, v_fn_5250_, v___x_5252_, v___x_5254_);
return v___x_5255_;
}
else
{
uint8_t v___x_5256_; 
v___x_5256_ = l_Lean_Expr_isConst(v_x_5247_);
if (v___x_5256_ == 0)
{
lean_dec_ref(v_x_5248_);
lean_dec_ref(v_x_5247_);
return v___x_5256_;
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; uint8_t v___x_5259_; 
v___x_5257_ = lean_unsigned_to_nat(0u);
v___x_5258_ = lean_array_get_size(v_fnNames_5246_);
v___x_5259_ = lean_nat_dec_lt(v___x_5257_, v___x_5258_);
if (v___x_5259_ == 0)
{
lean_dec_ref(v_x_5248_);
lean_dec_ref(v_x_5247_);
return v___x_5259_;
}
else
{
if (v___x_5259_ == 0)
{
lean_dec_ref(v_x_5248_);
lean_dec_ref(v_x_5247_);
return v___x_5259_;
}
else
{
size_t v___x_5260_; size_t v___x_5261_; uint8_t v___x_5262_; 
v___x_5260_ = ((size_t)0ULL);
v___x_5261_ = lean_usize_of_nat(v___x_5258_);
v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5247_, v_x_5248_, v_numSectionVars_5245_, v_fnNames_5246_, v___x_5260_, v___x_5261_);
lean_dec_ref(v_x_5248_);
lean_dec_ref(v_x_5247_);
return v___x_5262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5263_, lean_object* v_fnNames_5264_, lean_object* v_x_5265_, lean_object* v_x_5266_, lean_object* v_x_5267_){
_start:
{
uint8_t v_res_5268_; lean_object* v_r_5269_; 
v_res_5268_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5263_, v_fnNames_5264_, v_x_5265_, v_x_5266_, v_x_5267_);
lean_dec(v_x_5267_);
lean_dec_ref(v_fnNames_5264_);
lean_dec(v_numSectionVars_5263_);
v_r_5269_ = lean_box(v_res_5268_);
return v_r_5269_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5270_, lean_object* v_numSectionVars_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_dummy_5273_; lean_object* v_nargs_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; 
v_dummy_5273_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_5274_ = l_Lean_Expr_getAppNumArgs(v_a_5272_);
lean_inc(v_nargs_5274_);
v___x_5275_ = lean_mk_array(v_nargs_5274_, v_dummy_5273_);
v___x_5276_ = lean_unsigned_to_nat(1u);
v___x_5277_ = lean_nat_sub(v_nargs_5274_, v___x_5276_);
lean_dec(v_nargs_5274_);
v___x_5278_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5271_, v_fnNames_5270_, v_a_5272_, v___x_5275_, v___x_5277_);
lean_dec(v___x_5277_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5279_, lean_object* v_numSectionVars_5280_, lean_object* v_a_5281_){
_start:
{
uint8_t v_res_5282_; lean_object* v_r_5283_; 
v_res_5282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5279_, v_numSectionVars_5280_, v_a_5281_);
lean_dec(v_numSectionVars_5280_);
lean_dec_ref(v_fnNames_5279_);
v_r_5283_ = lean_box(v_res_5282_);
return v_r_5283_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5284_, lean_object* v_numSectionVars_5285_, lean_object* v_as_5286_, size_t v_i_5287_, size_t v_stop_5288_){
_start:
{
uint8_t v___x_5289_; 
v___x_5289_ = lean_usize_dec_eq(v_i_5287_, v_stop_5288_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; uint8_t v___x_5291_; 
v___x_5290_ = lean_array_uget_borrowed(v_as_5286_, v_i_5287_);
lean_inc(v___x_5290_);
v___x_5291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5284_, v_numSectionVars_5285_, v___x_5290_);
if (v___x_5291_ == 0)
{
size_t v___x_5292_; size_t v___x_5293_; 
v___x_5292_ = ((size_t)1ULL);
v___x_5293_ = lean_usize_add(v_i_5287_, v___x_5292_);
v_i_5287_ = v___x_5293_;
goto _start;
}
else
{
return v___x_5291_;
}
}
else
{
uint8_t v___x_5295_; 
v___x_5295_ = 0;
return v___x_5295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5296_, lean_object* v_numSectionVars_5297_, lean_object* v_as_5298_, lean_object* v_i_5299_, lean_object* v_stop_5300_){
_start:
{
size_t v_i_boxed_5301_; size_t v_stop_boxed_5302_; uint8_t v_res_5303_; lean_object* v_r_5304_; 
v_i_boxed_5301_ = lean_unbox_usize(v_i_5299_);
lean_dec(v_i_5299_);
v_stop_boxed_5302_ = lean_unbox_usize(v_stop_5300_);
lean_dec(v_stop_5300_);
v_res_5303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5296_, v_numSectionVars_5297_, v_as_5298_, v_i_boxed_5301_, v_stop_boxed_5302_);
lean_dec_ref(v_as_5298_);
lean_dec(v_numSectionVars_5297_);
lean_dec_ref(v_fnNames_5296_);
v_r_5304_ = lean_box(v_res_5303_);
return v_r_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5305_, lean_object* v_numSectionVars_5306_, lean_object* v___x_5307_, lean_object* v_x_5308_, lean_object* v_x_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
if (lean_obj_tag(v_x_5308_) == 5)
{
lean_object* v_fn_5316_; lean_object* v_arg_5317_; lean_object* v___x_5318_; 
v_fn_5316_ = lean_ctor_get(v_x_5308_, 0);
lean_inc_ref(v_fn_5316_);
v_arg_5317_ = lean_ctor_get(v_x_5308_, 1);
lean_inc_ref(v_arg_5317_);
lean_dec_ref_known(v_x_5308_, 2);
v___x_5318_ = lean_array_push(v_x_5309_, v_arg_5317_);
v_x_5308_ = v_fn_5316_;
v_x_5309_ = v___x_5318_;
goto _start;
}
else
{
uint8_t v___x_5320_; 
v___x_5320_ = l_Lean_Expr_isConst(v_x_5308_);
if (v___x_5320_ == 0)
{
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
lean_dec_ref(v___x_5307_);
goto v___jp_5313_;
}
else
{
lean_object* v___x_5321_; lean_object* v___x_5322_; uint8_t v___x_5323_; 
v___x_5321_ = lean_unsigned_to_nat(0u);
v___x_5322_ = lean_array_get_size(v_x_5309_);
v___x_5323_ = lean_nat_dec_lt(v___x_5321_, v___x_5322_);
if (v___x_5323_ == 0)
{
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
lean_dec_ref(v___x_5307_);
goto v___jp_5313_;
}
else
{
if (v___x_5323_ == 0)
{
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
lean_dec_ref(v___x_5307_);
goto v___jp_5313_;
}
else
{
size_t v___x_5324_; size_t v___x_5325_; uint8_t v___x_5326_; 
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = lean_usize_of_nat(v___x_5322_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5305_, v_numSectionVars_5306_, v_x_5309_, v___x_5324_, v___x_5325_);
if (v___x_5326_ == 0)
{
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
lean_dec_ref(v___x_5307_);
goto v___jp_5313_;
}
else
{
lean_object* v___x_5327_; uint8_t v___x_5328_; lean_object* v___x_5329_; 
v___x_5327_ = l_Lean_Expr_constName_x21(v_x_5308_);
v___x_5328_ = 0;
v___x_5329_ = l_Lean_Environment_find_x3f(v___x_5307_, v___x_5327_, v___x_5328_);
if (lean_obj_tag(v___x_5329_) == 1)
{
lean_object* v_val_5330_; 
v_val_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_val_5330_);
lean_dec_ref_known(v___x_5329_, 1);
if (lean_obj_tag(v_val_5330_) == 2)
{
lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5356_; 
v___x_5331_ = l_Lean_Expr_constLevels_x21(v_x_5308_);
lean_dec_ref(v_x_5308_);
v___x_5332_ = l_Lean_Core_instantiateValueLevelParams(v_val_5330_, v___x_5331_, v___x_5323_, v___y_5310_, v___y_5311_);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_val_5330_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v_val_5330_, 0);
lean_dec(v_unused_5357_);
v___x_5334_ = v_val_5330_;
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
else
{
lean_dec(v_val_5330_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
if (lean_obj_tag(v___x_5332_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5347_; 
v_a_5336_ = lean_ctor_get(v___x_5332_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5338_ = v___x_5332_;
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5332_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; lean_object* v___x_5342_; 
v___x_5340_ = l_Lean_Expr_betaRev(v_a_5336_, v_x_5309_, v___x_5328_, v___x_5328_);
lean_dec_ref(v_x_5309_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set_tag(v___x_5334_, 1);
lean_ctor_set(v___x_5334_, 0, v___x_5340_);
v___x_5342_ = v___x_5334_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5340_);
v___x_5342_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5344_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5342_);
v___x_5344_ = v___x_5338_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5342_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
else
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
lean_del_object(v___x_5334_);
lean_dec_ref(v_x_5309_);
v_a_5348_ = lean_ctor_get(v___x_5332_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5332_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5332_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
}
else
{
lean_dec(v_val_5330_);
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
goto v___jp_5313_;
}
}
else
{
lean_dec(v___x_5329_);
lean_dec_ref(v_x_5309_);
lean_dec_ref(v_x_5308_);
goto v___jp_5313_;
}
}
}
}
}
}
v___jp_5313_:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5314_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5314_);
return v___x_5315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5358_, lean_object* v_numSectionVars_5359_, lean_object* v___x_5360_, lean_object* v_x_5361_, lean_object* v_x_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5358_, v_numSectionVars_5359_, v___x_5360_, v_x_5361_, v_x_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v_numSectionVars_5359_);
lean_dec_ref(v_fnNames_5358_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5367_, lean_object* v_numSectionVars_5368_, lean_object* v_env_5369_, lean_object* v_e_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5374_ = l_Lean_Expr_getAppNumArgs(v_e_5370_);
v___x_5375_ = lean_mk_empty_array_with_capacity(v___x_5374_);
lean_dec(v___x_5374_);
v___x_5376_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5367_, v_numSectionVars_5368_, v_env_5369_, v_e_5370_, v___x_5375_, v___y_5371_, v___y_5372_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5377_, lean_object* v_numSectionVars_5378_, lean_object* v_env_5379_, lean_object* v_e_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5377_, v_numSectionVars_5378_, v_env_5379_, v_e_5380_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v_numSectionVars_5378_);
lean_dec_ref(v_fnNames_5377_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5385_, lean_object* v_numSectionVars_5386_, lean_object* v_e_5387_, lean_object* v___f_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v___x_5392_; lean_object* v_env_5393_; lean_object* v___f_5394_; lean_object* v___x_5395_; 
v___x_5392_ = lean_st_ref_get(v___y_5390_);
v_env_5393_ = lean_ctor_get(v___x_5392_, 0);
lean_inc_ref(v_env_5393_);
lean_dec(v___x_5392_);
v___f_5394_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5394_, 0, v_fnNames_5385_);
lean_closure_set(v___f_5394_, 1, v_numSectionVars_5386_);
lean_closure_set(v___f_5394_, 2, v_env_5393_);
v___x_5395_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5387_, v___f_5394_, v___f_5388_, v___y_5389_, v___y_5390_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5396_, lean_object* v_numSectionVars_5397_, lean_object* v_e_5398_, lean_object* v___f_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5396_, v_numSectionVars_5397_, v_e_5398_, v___f_5399_, v___y_5400_, v___y_5401_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5404_, uint8_t v_isExporting_5405_, lean_object* v___x_5406_, lean_object* v_a_x3f_5407_){
_start:
{
lean_object* v___x_5409_; lean_object* v_env_5410_; lean_object* v_nextMacroScope_5411_; lean_object* v_ngen_5412_; lean_object* v_auxDeclNGen_5413_; lean_object* v_traceState_5414_; lean_object* v_recordedDeps_5415_; lean_object* v_messages_5416_; lean_object* v_infoState_5417_; lean_object* v_snapshotTasks_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5429_; 
v___x_5409_ = lean_st_ref_take(v___y_5404_);
v_env_5410_ = lean_ctor_get(v___x_5409_, 0);
v_nextMacroScope_5411_ = lean_ctor_get(v___x_5409_, 1);
v_ngen_5412_ = lean_ctor_get(v___x_5409_, 2);
v_auxDeclNGen_5413_ = lean_ctor_get(v___x_5409_, 3);
v_traceState_5414_ = lean_ctor_get(v___x_5409_, 4);
v_recordedDeps_5415_ = lean_ctor_get(v___x_5409_, 6);
v_messages_5416_ = lean_ctor_get(v___x_5409_, 7);
v_infoState_5417_ = lean_ctor_get(v___x_5409_, 8);
v_snapshotTasks_5418_ = lean_ctor_get(v___x_5409_, 9);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; 
v_unused_5430_ = lean_ctor_get(v___x_5409_, 5);
lean_dec(v_unused_5430_);
v___x_5420_ = v___x_5409_;
v_isShared_5421_ = v_isSharedCheck_5429_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_snapshotTasks_5418_);
lean_inc(v_infoState_5417_);
lean_inc(v_messages_5416_);
lean_inc(v_recordedDeps_5415_);
lean_inc(v_traceState_5414_);
lean_inc(v_auxDeclNGen_5413_);
lean_inc(v_ngen_5412_);
lean_inc(v_nextMacroScope_5411_);
lean_inc(v_env_5410_);
lean_dec(v___x_5409_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5429_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5425_; 
v___x_5422_ = lean_box(0);
v___x_5423_ = l_Lean_Environment_setExporting(v_env_5410_, v_isExporting_5405_);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 5, v___x_5406_);
lean_ctor_set(v___x_5420_, 0, v___x_5423_);
v___x_5425_ = v___x_5420_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5423_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v_nextMacroScope_5411_);
lean_ctor_set(v_reuseFailAlloc_5428_, 2, v_ngen_5412_);
lean_ctor_set(v_reuseFailAlloc_5428_, 3, v_auxDeclNGen_5413_);
lean_ctor_set(v_reuseFailAlloc_5428_, 4, v_traceState_5414_);
lean_ctor_set(v_reuseFailAlloc_5428_, 5, v___x_5406_);
lean_ctor_set(v_reuseFailAlloc_5428_, 6, v_recordedDeps_5415_);
lean_ctor_set(v_reuseFailAlloc_5428_, 7, v_messages_5416_);
lean_ctor_set(v_reuseFailAlloc_5428_, 8, v_infoState_5417_);
lean_ctor_set(v_reuseFailAlloc_5428_, 9, v_snapshotTasks_5418_);
v___x_5425_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5426_ = lean_st_ref_put(v___y_5404_, v___x_5425_);
v___x_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5422_);
return v___x_5427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5431_, lean_object* v_isExporting_5432_, lean_object* v___x_5433_, lean_object* v_a_x3f_5434_, lean_object* v___y_5435_){
_start:
{
uint8_t v_isExporting_boxed_5436_; lean_object* v_res_5437_; 
v_isExporting_boxed_5436_ = lean_unbox(v_isExporting_5432_);
v_res_5437_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5431_, v_isExporting_boxed_5436_, v___x_5433_, v_a_x3f_5434_);
lean_dec(v_a_x3f_5434_);
lean_dec(v___y_5431_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5438_, uint8_t v_isExporting_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
lean_object* v___x_5443_; lean_object* v_env_5444_; lean_object* v___x_5445_; uint8_t v_isModule_5446_; 
v___x_5443_ = lean_st_ref_get(v___y_5441_);
v_env_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc_ref(v_env_5444_);
lean_dec(v___x_5443_);
v___x_5445_ = l_Lean_Environment_header(v_env_5444_);
v_isModule_5446_ = lean_ctor_get_uint8(v___x_5445_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5445_);
if (v_isModule_5446_ == 0)
{
lean_object* v___x_5447_; 
lean_dec_ref(v_env_5444_);
lean_inc(v___y_5441_);
lean_inc_ref(v___y_5440_);
v___x_5447_ = lean_apply_3(v_x_5438_, v___y_5440_, v___y_5441_, lean_box(0));
return v___x_5447_;
}
else
{
uint8_t v_isExporting_5448_; 
v_isExporting_5448_ = lean_ctor_get_uint8(v_env_5444_, sizeof(void*)*13);
lean_dec_ref(v_env_5444_);
if (v_isExporting_5439_ == 0)
{
if (v_isExporting_5448_ == 0)
{
lean_object* v___x_5500_; 
lean_inc(v___y_5441_);
lean_inc_ref(v___y_5440_);
v___x_5500_ = lean_apply_3(v_x_5438_, v___y_5440_, v___y_5441_, lean_box(0));
return v___x_5500_;
}
else
{
goto v___jp_5449_;
}
}
else
{
if (v_isExporting_5448_ == 0)
{
goto v___jp_5449_;
}
else
{
lean_object* v___x_5501_; 
lean_inc(v___y_5441_);
lean_inc_ref(v___y_5440_);
v___x_5501_ = lean_apply_3(v_x_5438_, v___y_5440_, v___y_5441_, lean_box(0));
return v___x_5501_;
}
}
v___jp_5449_:
{
lean_object* v___x_5450_; lean_object* v_env_5451_; lean_object* v_nextMacroScope_5452_; lean_object* v_ngen_5453_; lean_object* v_auxDeclNGen_5454_; lean_object* v_traceState_5455_; lean_object* v_recordedDeps_5456_; lean_object* v_messages_5457_; lean_object* v_infoState_5458_; lean_object* v_snapshotTasks_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5498_; 
v___x_5450_ = lean_st_ref_take(v___y_5441_);
v_env_5451_ = lean_ctor_get(v___x_5450_, 0);
v_nextMacroScope_5452_ = lean_ctor_get(v___x_5450_, 1);
v_ngen_5453_ = lean_ctor_get(v___x_5450_, 2);
v_auxDeclNGen_5454_ = lean_ctor_get(v___x_5450_, 3);
v_traceState_5455_ = lean_ctor_get(v___x_5450_, 4);
v_recordedDeps_5456_ = lean_ctor_get(v___x_5450_, 6);
v_messages_5457_ = lean_ctor_get(v___x_5450_, 7);
v_infoState_5458_ = lean_ctor_get(v___x_5450_, 8);
v_snapshotTasks_5459_ = lean_ctor_get(v___x_5450_, 9);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; 
v_unused_5499_ = lean_ctor_get(v___x_5450_, 5);
lean_dec(v_unused_5499_);
v___x_5461_ = v___x_5450_;
v_isShared_5462_ = v_isSharedCheck_5498_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_snapshotTasks_5459_);
lean_inc(v_infoState_5458_);
lean_inc(v_messages_5457_);
lean_inc(v_recordedDeps_5456_);
lean_inc(v_traceState_5455_);
lean_inc(v_auxDeclNGen_5454_);
lean_inc(v_ngen_5453_);
lean_inc(v_nextMacroScope_5452_);
lean_inc(v_env_5451_);
lean_dec(v___x_5450_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5498_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5466_; 
v___x_5463_ = l_Lean_Environment_setExporting(v_env_5451_, v_isExporting_5439_);
v___x_5464_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 5, v___x_5464_);
lean_ctor_set(v___x_5461_, 0, v___x_5463_);
v___x_5466_ = v___x_5461_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5463_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v_nextMacroScope_5452_);
lean_ctor_set(v_reuseFailAlloc_5497_, 2, v_ngen_5453_);
lean_ctor_set(v_reuseFailAlloc_5497_, 3, v_auxDeclNGen_5454_);
lean_ctor_set(v_reuseFailAlloc_5497_, 4, v_traceState_5455_);
lean_ctor_set(v_reuseFailAlloc_5497_, 5, v___x_5464_);
lean_ctor_set(v_reuseFailAlloc_5497_, 6, v_recordedDeps_5456_);
lean_ctor_set(v_reuseFailAlloc_5497_, 7, v_messages_5457_);
lean_ctor_set(v_reuseFailAlloc_5497_, 8, v_infoState_5458_);
lean_ctor_set(v_reuseFailAlloc_5497_, 9, v_snapshotTasks_5459_);
v___x_5466_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5467_; lean_object* v_r_5468_; 
v___x_5467_ = lean_st_ref_put(v___y_5441_, v___x_5466_);
lean_inc(v___y_5441_);
lean_inc_ref(v___y_5440_);
v_r_5468_ = lean_apply_3(v_x_5438_, v___y_5440_, v___y_5441_, lean_box(0));
if (lean_obj_tag(v_r_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5485_; 
v_a_5469_ = lean_ctor_get(v_r_5468_, 0);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_r_5468_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5471_ = v_r_5468_;
v_isShared_5472_ = v_isSharedCheck_5485_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v_r_5468_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5485_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
lean_inc(v_a_5469_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set_tag(v___x_5471_, 1);
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_a_5469_);
v___x_5474_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
v___x_5475_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5441_, v_isExporting_5448_, v___x_5464_, v___x_5474_);
lean_dec_ref(v___x_5474_);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5475_);
if (v_isSharedCheck_5482_ == 0)
{
lean_object* v_unused_5483_; 
v_unused_5483_ = lean_ctor_get(v___x_5475_, 0);
lean_dec(v_unused_5483_);
v___x_5477_ = v___x_5475_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_dec(v___x_5475_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 0, v_a_5469_);
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5469_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
}
else
{
lean_object* v_a_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5495_; 
v_a_5486_ = lean_ctor_get(v_r_5468_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v_r_5468_, 1);
v___x_5487_ = lean_box(0);
v___x_5488_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5441_, v_isExporting_5448_, v___x_5464_, v___x_5487_);
v_isSharedCheck_5495_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5495_ == 0)
{
lean_object* v_unused_5496_; 
v_unused_5496_ = lean_ctor_get(v___x_5488_, 0);
lean_dec(v_unused_5496_);
v___x_5490_ = v___x_5488_;
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
else
{
lean_dec(v___x_5488_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5493_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set_tag(v___x_5490_, 1);
lean_ctor_set(v___x_5490_, 0, v_a_5486_);
v___x_5493_ = v___x_5490_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_a_5486_);
v___x_5493_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
return v___x_5493_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5502_, lean_object* v_isExporting_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
uint8_t v_isExporting_boxed_5507_; lean_object* v_res_5508_; 
v_isExporting_boxed_5507_ = lean_unbox(v_isExporting_5503_);
v_res_5508_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5502_, v_isExporting_boxed_5507_, v___y_5504_, v___y_5505_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5509_, uint8_t v_when_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_){
_start:
{
if (v_when_5510_ == 0)
{
lean_object* v___x_5514_; 
lean_inc(v___y_5512_);
lean_inc_ref(v___y_5511_);
v___x_5514_ = lean_apply_3(v_x_5509_, v___y_5511_, v___y_5512_, lean_box(0));
return v___x_5514_;
}
else
{
uint8_t v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = 0;
v___x_5516_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5509_, v___x_5515_, v___y_5511_, v___y_5512_);
return v___x_5516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5517_, lean_object* v_when_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_){
_start:
{
uint8_t v_when_boxed_5522_; lean_object* v_res_5523_; 
v_when_boxed_5522_ = lean_unbox(v_when_5518_);
v_res_5523_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5517_, v_when_boxed_5522_, v___y_5519_, v___y_5520_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5524_, lean_object* v_numSectionVars_5525_, lean_object* v_e_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_){
_start:
{
lean_object* v___f_5530_; lean_object* v___f_5531_; uint8_t v___x_5532_; lean_object* v___x_5533_; 
v___f_5530_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5531_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5531_, 0, v_fnNames_5524_);
lean_closure_set(v___f_5531_, 1, v_numSectionVars_5525_);
lean_closure_set(v___f_5531_, 2, v_e_5526_);
lean_closure_set(v___f_5531_, 3, v___f_5530_);
v___x_5532_ = 1;
v___x_5533_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5531_, v___x_5532_, v_a_5527_, v_a_5528_);
return v___x_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5534_, lean_object* v_numSectionVars_5535_, lean_object* v_e_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5534_, v_numSectionVars_5535_, v_e_5536_, v_a_5537_, v_a_5538_);
lean_dec(v_a_5538_);
lean_dec_ref(v_a_5537_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5541_, lean_object* v_x_5542_, uint8_t v_isExporting_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v___x_5547_; 
v___x_5547_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5542_, v_isExporting_5543_, v___y_5544_, v___y_5545_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5548_, lean_object* v_x_5549_, lean_object* v_isExporting_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_){
_start:
{
uint8_t v_isExporting_boxed_5554_; lean_object* v_res_5555_; 
v_isExporting_boxed_5554_ = lean_unbox(v_isExporting_5550_);
v_res_5555_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5548_, v_x_5549_, v_isExporting_boxed_5554_, v___y_5551_, v___y_5552_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
return v_res_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5556_, lean_object* v_x_5557_, uint8_t v_when_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5557_, v_when_5558_, v___y_5559_, v___y_5560_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5563_, lean_object* v_x_5564_, lean_object* v_when_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_){
_start:
{
uint8_t v_when_boxed_5569_; lean_object* v_res_5570_; 
v_when_boxed_5569_ = lean_unbox(v_when_5565_);
v_res_5570_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5563_, v_x_5564_, v_when_boxed_5569_, v___y_5566_, v___y_5567_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
return v_res_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_){
_start:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5575_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
lean_object* v_res_5581_; 
v_res_5581_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5577_, v___y_5578_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec_ref(v_x_5577_);
return v_res_5581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v___y_5587_; lean_object* v___x_5590_; 
v___x_5590_ = l_Lean_inaccessible_x3f(v_e_5582_);
if (lean_obj_tag(v___x_5590_) == 1)
{
lean_object* v_val_5591_; 
lean_dec_ref(v_e_5582_);
v_val_5591_ = lean_ctor_get(v___x_5590_, 0);
lean_inc(v_val_5591_);
lean_dec_ref_known(v___x_5590_, 1);
v___y_5587_ = v_val_5591_;
goto v___jp_5586_;
}
else
{
lean_dec(v___x_5590_);
v___y_5587_ = v_e_5582_;
goto v___jp_5586_;
}
v___jp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5588_, 0, v___y_5587_);
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
return v___x_5589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5592_, v___y_5593_, v___y_5594_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_){
_start:
{
lean_object* v___f_5603_; lean_object* v___f_5604_; lean_object* v___x_5605_; 
v___f_5603_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5604_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5605_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5599_, v___f_5603_, v___f_5604_, v_a_5600_, v_a_5601_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_){
_start:
{
lean_object* v___y_5616_; lean_object* v___x_5619_; 
v___x_5619_ = l_Lean_patternWithRef_x3f(v_e_5611_);
if (lean_obj_tag(v___x_5619_) == 1)
{
lean_object* v_val_5620_; lean_object* v_snd_5621_; 
lean_dec_ref(v_e_5611_);
v_val_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_val_5620_);
lean_dec_ref_known(v___x_5619_, 1);
v_snd_5621_ = lean_ctor_get(v_val_5620_, 1);
lean_inc(v_snd_5621_);
lean_dec(v_val_5620_);
v___y_5616_ = v_snd_5621_;
goto v___jp_5615_;
}
else
{
lean_dec(v___x_5619_);
v___y_5616_ = v_e_5611_;
goto v___jp_5615_;
}
v___jp_5615_:
{
lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5617_, 0, v___y_5616_);
v___x_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5617_);
return v___x_5618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_){
_start:
{
lean_object* v_res_5626_; 
v_res_5626_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5622_, v___y_5623_, v___y_5624_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_){
_start:
{
lean_object* v___f_5632_; lean_object* v___f_5633_; lean_object* v___x_5634_; 
v___f_5632_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5633_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5634_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5628_, v___f_5632_, v___f_5633_, v_a_5629_, v_a_5630_);
return v___x_5634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5635_, v_a_5636_, v_a_5637_);
lean_dec(v_a_5637_);
lean_dec_ref(v_a_5636_);
return v_res_5639_;
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
