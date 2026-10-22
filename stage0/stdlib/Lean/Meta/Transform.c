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
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value)} };
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
lean_object* v___y_1097_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1111_; uint16_t v___y_1112_; lean_object* v_toCold_1117_; lean_object* v_currRecDepth_1118_; lean_object* v_ref_1119_; uint16_t v_optionFlags_1120_; uint8_t v_suppressElabErrors_1121_; uint8_t v_isRecordingDeps_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_cancelTk_x3f_1124_; 
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
v___x_1114_ = lean_nat_add(v___y_1108_, v___x_1113_);
lean_inc_ref(v___y_1107_);
v___x_1115_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1115_, 0, v___y_1107_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
lean_ctor_set(v___x_1115_, 2, v___y_1111_);
lean_ctor_set_uint16(v___x_1115_, sizeof(void*)*3, v___y_1112_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*3 + 2, v___y_1109_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*3 + 3, v___y_1110_);
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
v___y_1107_ = v_toCold_1117_;
v___y_1108_ = v_currRecDepth_1118_;
v___y_1109_ = v_suppressElabErrors_1121_;
v___y_1110_ = v_isRecordingDeps_1122_;
v___y_1111_ = v_ref_1119_;
v___y_1112_ = v_optionFlags_1120_;
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
v___y_1107_ = v_toCold_1117_;
v___y_1108_ = v_currRecDepth_1118_;
v___y_1109_ = v_suppressElabErrors_1121_;
v___y_1110_ = v_isRecordingDeps_1122_;
v___y_1111_ = v_ref_1119_;
v___y_1112_ = v_optionFlags_1120_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_declName_1808_, lean_object* v_a_1809_, lean_object* v___f_1810_, uint8_t v_nondep_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
uint8_t v___x_1814_; lean_object* v___x_3461__overap_1815_; lean_object* v___x_1816_; 
v___x_1814_ = 0;
v___x_3461__overap_1815_ = l_Lean_Meta_withLetDecl___redArg(v___x_1806_, v___x_1807_, v_declName_1808_, v_a_1809_, v_a_1813_, v___f_1810_, v_nondep_1811_, v___x_1814_);
lean_inc(v_a_1812_);
v___x_1816_ = lean_apply_1(v___x_3461__overap_1815_, v_a_1812_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1817_, lean_object* v___x_1818_, lean_object* v_declName_1819_, lean_object* v_a_1820_, lean_object* v___f_1821_, lean_object* v_nondep_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
uint8_t v_nondep_3570__boxed_1825_; lean_object* v_res_1826_; 
v_nondep_3570__boxed_1825_ = lean_unbox(v_nondep_1822_);
v_res_1826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1817_, v___x_1818_, v_declName_1819_, v_a_1820_, v___f_1821_, v_nondep_3570__boxed_1825_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1827_, uint8_t v_usedLetOnly_1828_, lean_object* v_inst_1829_, lean_object* v_toBind_1830_, lean_object* v___f_1831_, lean_object* v_a_1832_){
_start:
{
uint8_t v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1833_ = 0;
v___x_1834_ = 1;
v___x_1835_ = lean_box(v_usedLetOnly_1828_);
v___x_1836_ = lean_box(v___x_1833_);
v___x_1837_ = lean_box(v___x_1834_);
v___x_1838_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1838_, 0, v_fvars_1827_);
lean_closure_set(v___x_1838_, 1, v_a_1832_);
lean_closure_set(v___x_1838_, 2, v___x_1835_);
lean_closure_set(v___x_1838_, 3, v___x_1836_);
lean_closure_set(v___x_1838_, 4, v___x_1837_);
v___x_1839_ = lean_apply_2(v_inst_1829_, lean_box(0), v___x_1838_);
v___x_1840_ = lean_apply_4(v_toBind_1830_, lean_box(0), lean_box(0), v___x_1839_, v___f_1831_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1841_, lean_object* v_usedLetOnly_1842_, lean_object* v_inst_1843_, lean_object* v_toBind_1844_, lean_object* v___f_1845_, lean_object* v_a_1846_){
_start:
{
uint8_t v_usedLetOnly_boxed_1847_; lean_object* v_res_1848_; 
v_usedLetOnly_boxed_1847_ = lean_unbox(v_usedLetOnly_1842_);
v_res_1848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1841_, v_usedLetOnly_boxed_1847_, v_inst_1843_, v_toBind_1844_, v___f_1845_, v_a_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1849_, uint8_t v_usedLetOnly_1850_, lean_object* v_inst_1851_, lean_object* v_toBind_1852_, lean_object* v___f_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v___x_1855_; uint8_t v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1855_ = 0;
v___x_1856_ = 1;
v___x_1857_ = 1;
v___x_1858_ = lean_box(v___x_1855_);
v___x_1859_ = lean_box(v_usedLetOnly_1850_);
v___x_1860_ = lean_box(v___x_1855_);
v___x_1861_ = lean_box(v___x_1856_);
v___x_1862_ = lean_box(v___x_1857_);
v___x_1863_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1863_, 0, v_fvars_1849_);
lean_closure_set(v___x_1863_, 1, v_a_1854_);
lean_closure_set(v___x_1863_, 2, v___x_1858_);
lean_closure_set(v___x_1863_, 3, v___x_1859_);
lean_closure_set(v___x_1863_, 4, v___x_1860_);
lean_closure_set(v___x_1863_, 5, v___x_1861_);
lean_closure_set(v___x_1863_, 6, v___x_1862_);
v___x_1864_ = lean_apply_2(v_inst_1851_, lean_box(0), v___x_1863_);
v___x_1865_ = lean_apply_4(v_toBind_1852_, lean_box(0), lean_box(0), v___x_1864_, v___f_1853_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1866_, lean_object* v_usedLetOnly_1867_, lean_object* v_inst_1868_, lean_object* v_toBind_1869_, lean_object* v___f_1870_, lean_object* v_a_1871_){
_start:
{
uint8_t v_usedLetOnly_boxed_1872_; lean_object* v_res_1873_; 
v_usedLetOnly_boxed_1872_ = lean_unbox(v_usedLetOnly_1867_);
v_res_1873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1866_, v_usedLetOnly_boxed_1872_, v_inst_1868_, v_toBind_1869_, v___f_1870_, v_a_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1874_, lean_object* v___x_1875_, lean_object* v_binderName_1876_, uint8_t v_binderInfo_1877_, lean_object* v___f_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
uint8_t v___x_1881_; lean_object* v___x_3519__overap_1882_; lean_object* v___x_1883_; 
v___x_1881_ = 0;
v___x_3519__overap_1882_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1874_, v___x_1875_, v_binderName_1876_, v_binderInfo_1877_, v_a_1880_, v___f_1878_, v___x_1881_);
lean_inc(v_a_1879_);
v___x_1883_ = lean_apply_1(v___x_3519__overap_1882_, v_a_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1884_, lean_object* v___x_1885_, lean_object* v_binderName_1886_, lean_object* v_binderInfo_1887_, lean_object* v___f_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
uint8_t v_binderInfo_3638__boxed_1891_; lean_object* v_res_1892_; 
v_binderInfo_3638__boxed_1891_ = lean_unbox(v_binderInfo_1887_);
v_res_1892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1884_, v___x_1885_, v_binderName_1886_, v_binderInfo_3638__boxed_1891_, v___f_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_f_1893_, lean_object* v_postApp_1894_, lean_object* v___y_1895_, lean_object* v_toBind_1896_, lean_object* v___f_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = l_Lean_mkAppN(v_f_1893_, v_a_1898_);
v___x_1900_ = lean_apply_2(v_postApp_1894_, v___y_1895_, v___x_1899_);
v___x_1901_ = lean_apply_4(v_toBind_1896_, lean_box(0), lean_box(0), v___x_1900_, v___f_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_f_1902_, lean_object* v_postApp_1903_, lean_object* v___y_1904_, lean_object* v_toBind_1905_, lean_object* v___f_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_f_1902_, v_postApp_1903_, v___y_1904_, v_toBind_1905_, v___f_1906_, v_a_1907_);
lean_dec_ref(v_a_1907_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v_toApplicative_1909_, lean_object* v_next_1910_, lean_object* v_G_1911_, lean_object* v___y_1912_, lean_object* v_a_1913_){
_start:
{
if (lean_obj_tag(v_a_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v_toPure_1915_; lean_object* v___x_1916_; 
lean_dec(v_G_1911_);
v_a_1914_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v_a_1913_, 1);
v_toPure_1915_ = lean_ctor_get(v_toApplicative_1909_, 1);
lean_inc(v_toPure_1915_);
lean_dec_ref(v_toApplicative_1909_);
v___x_1916_ = lean_apply_2(v_toPure_1915_, lean_box(0), v_a_1914_);
return v___x_1916_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_toApplicative_1909_);
v_a_1917_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v_a_1913_, 1);
v___x_1918_ = lean_unsigned_to_nat(1u);
v___x_1919_ = lean_nat_add(v_next_1910_, v___x_1918_);
lean_inc(v___y_1912_);
v___x_1920_ = lean_apply_5(v_G_1911_, v___x_1919_, v_a_1917_, lean_box(0), lean_box(0), v___y_1912_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_1921_, lean_object* v_next_1922_, lean_object* v_G_1923_, lean_object* v___y_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v_toApplicative_1921_, v_next_1922_, v_G_1923_, v___y_1924_, v_a_1925_);
lean_dec(v___y_1924_);
lean_dec(v_next_1922_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1927_, lean_object* v_acc_1928_, lean_object* v_next_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_toPure_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_toPure_1931_ = lean_ctor_get(v_toApplicative_1927_, 1);
lean_inc(v_toPure_1931_);
lean_dec_ref(v_toApplicative_1927_);
v___x_1932_ = lean_array_fset(v_acc_1928_, v_next_1929_, v_a_1930_);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
v___x_1934_ = lean_apply_2(v_toPure_1931_, lean_box(0), v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_1935_, lean_object* v_acc_1936_, lean_object* v_next_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_1935_, v_acc_1936_, v_next_1937_, v_a_1938_);
lean_dec(v_next_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v___f_1940_, lean_object* v___y_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v___x_1943_; 
lean_inc(v___y_1941_);
v___x_1943_ = lean_apply_2(v___f_1940_, v_a_1942_, v___y_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v___f_1944_, lean_object* v___y_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v___f_1944_, v___y_1945_, v_a_1946_);
lean_dec(v___y_1945_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v___x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Core_checkSystem(v___x_1972_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v___x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v___x_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15(lean_object* v_inst_1988_, lean_object* v_x_1989_, lean_object* v___x_1990_, lean_object* v___x_1991_, lean_object* v_inst_1992_, lean_object* v___f_1993_, lean_object* v___x_1994_, lean_object* v___x_1995_, lean_object* v_a_1996_, lean_object* v_toBind_1997_, lean_object* v___f_1998_, lean_object* v_toApplicative_1999_, lean_object* v_a_2000_){
_start:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_3442__overap_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec_ref(v_toApplicative_1999_);
v___f_2001_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___closed__0));
v___x_2002_ = lean_apply_2(v_inst_1988_, lean_box(0), v___f_2001_);
lean_inc_ref(v___x_1991_);
lean_inc_ref(v___x_1990_);
v___x_2003_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_2003_, 0, lean_box(0));
lean_closure_set(v___x_2003_, 1, lean_box(0));
lean_closure_set(v___x_2003_, 2, lean_box(0));
lean_closure_set(v___x_2003_, 3, lean_box(0));
lean_closure_set(v___x_2003_, 4, v_x_1989_);
lean_closure_set(v___x_2003_, 5, v___x_1990_);
lean_closure_set(v___x_2003_, 6, v___x_1991_);
lean_closure_set(v___x_2003_, 7, lean_box(0));
lean_closure_set(v___x_2003_, 8, v___x_2002_);
v___x_2004_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_2004_, 0, lean_box(0));
lean_closure_set(v___x_2004_, 1, lean_box(0));
lean_closure_set(v___x_2004_, 2, lean_box(0));
lean_closure_set(v___x_2004_, 3, lean_box(0));
lean_closure_set(v___x_2004_, 4, v_x_1989_);
lean_closure_set(v___x_2004_, 5, v___x_1990_);
lean_closure_set(v___x_2004_, 6, v___x_1991_);
lean_closure_set(v___x_2004_, 7, v_inst_1992_);
lean_closure_set(v___x_2004_, 8, lean_box(0));
lean_closure_set(v___x_2004_, 9, lean_box(0));
lean_closure_set(v___x_2004_, 10, v___x_2003_);
lean_closure_set(v___x_2004_, 11, v___f_1993_);
v___x_3442__overap_2005_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1994_, v___x_1995_, v___x_2004_);
lean_inc(v_a_1996_);
v___x_2006_ = lean_apply_1(v___x_3442__overap_2005_, v_a_1996_);
v___x_2007_ = lean_apply_4(v_toBind_1997_, lean_box(0), lean_box(0), v___x_2006_, v___f_1998_);
return v___x_2007_;
}
else
{
lean_object* v_val_2008_; lean_object* v_toPure_2009_; lean_object* v___x_2010_; 
lean_dec(v___f_1998_);
lean_dec(v_toBind_1997_);
lean_dec_ref(v___x_1995_);
lean_dec_ref(v___x_1994_);
lean_dec(v___f_1993_);
lean_dec_ref(v_inst_1992_);
lean_dec_ref(v___x_1991_);
lean_dec_ref(v___x_1990_);
lean_dec(v_inst_1988_);
v_val_2008_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_a_2000_, 1);
v_toPure_2009_ = lean_ctor_get(v_toApplicative_1999_, 1);
lean_inc(v_toPure_2009_);
lean_dec_ref(v_toApplicative_1999_);
v___x_2010_ = lean_apply_2(v_toPure_2009_, lean_box(0), v_val_2008_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___boxed(lean_object* v_inst_2011_, lean_object* v_x_2012_, lean_object* v___x_2013_, lean_object* v___x_2014_, lean_object* v_inst_2015_, lean_object* v___f_2016_, lean_object* v___x_2017_, lean_object* v___x_2018_, lean_object* v_a_2019_, lean_object* v_toBind_2020_, lean_object* v___f_2021_, lean_object* v_toApplicative_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15(v_inst_2011_, v_x_2012_, v___x_2013_, v___x_2014_, v_inst_2015_, v___f_2016_, v___x_2017_, v___x_2018_, v_a_2019_, v_toBind_2020_, v___f_2021_, v_toApplicative_2022_, v_a_2023_);
lean_dec(v_a_2019_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_pre_2031_, lean_object* v_post_2032_, uint8_t v_usedLetOnly_2033_, uint8_t v_skipConstInApp_2034_, uint8_t v_skipInstances_2035_, lean_object* v_postApp_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_body_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_array_push(v_fvars_2027_, v_x_2040_);
v___x_2043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2028_, v_inst_2029_, v_inst_2030_, v_pre_2031_, v_post_2032_, v_usedLetOnly_2033_, v_skipConstInApp_2034_, v_skipInstances_2035_, v_postApp_2036_, v_x_2037_, v_x_2038_, v___x_2042_, v_body_2039_, v___y_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_pre_2048_, lean_object* v_post_2049_, lean_object* v_usedLetOnly_2050_, lean_object* v_skipConstInApp_2051_, lean_object* v_skipInstances_2052_, lean_object* v_postApp_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_body_2056_, lean_object* v_x_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_usedLetOnly_boxed_2059_; uint8_t v_skipConstInApp_boxed_2060_; uint8_t v_skipInstances_boxed_2061_; lean_object* v_res_2062_; 
v_usedLetOnly_boxed_2059_ = lean_unbox(v_usedLetOnly_2050_);
v_skipConstInApp_boxed_2060_ = lean_unbox(v_skipConstInApp_2051_);
v_skipInstances_boxed_2061_ = lean_unbox(v_skipInstances_2052_);
v_res_2062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2044_, v_inst_2045_, v_inst_2046_, v_inst_2047_, v_pre_2048_, v_post_2049_, v_usedLetOnly_boxed_2059_, v_skipConstInApp_boxed_2060_, v_skipInstances_boxed_2061_, v_postApp_2053_, v_x_2054_, v_x_2055_, v_body_2056_, v_x_2057_, v___y_2058_);
lean_dec(v___y_2058_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_pre_2066_, lean_object* v_post_2067_, uint8_t v_usedLetOnly_2068_, uint8_t v_skipConstInApp_2069_, uint8_t v_skipInstances_2070_, lean_object* v_postApp_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2063_, v_inst_2064_, v_inst_2065_, v_pre_2066_, v_post_2067_, v_usedLetOnly_2068_, v_skipConstInApp_2069_, v_skipInstances_2070_, v_postApp_2071_, v_x_2072_, v_x_2073_, v_a_2075_, v_a_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_pre_2080_, lean_object* v_post_2081_, lean_object* v_usedLetOnly_2082_, lean_object* v_skipConstInApp_2083_, lean_object* v_skipInstances_2084_, lean_object* v_postApp_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
uint8_t v_usedLetOnly_boxed_2090_; uint8_t v_skipConstInApp_boxed_2091_; uint8_t v_skipInstances_boxed_2092_; lean_object* v_res_2093_; 
v_usedLetOnly_boxed_2090_ = lean_unbox(v_usedLetOnly_2082_);
v_skipConstInApp_boxed_2091_ = lean_unbox(v_skipConstInApp_2083_);
v_skipInstances_boxed_2092_ = lean_unbox(v_skipInstances_2084_);
v_res_2093_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2077_, v_inst_2078_, v_inst_2079_, v_pre_2080_, v_post_2081_, v_usedLetOnly_boxed_2090_, v_skipConstInApp_boxed_2091_, v_skipInstances_boxed_2092_, v_postApp_2085_, v_x_2086_, v_x_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_pre_2097_, lean_object* v_post_2098_, uint8_t v_usedLetOnly_2099_, uint8_t v_skipConstInApp_2100_, uint8_t v_skipInstances_2101_, lean_object* v_postApp_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_fvars_2105_, lean_object* v_e_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___f_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2094_);
v___x_2110_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2103_, v___x_2108_, v___x_2109_, v_inst_2094_);
v___x_2111_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2103_, v___x_2108_, v___x_2109_);
lean_inc_ref_n(v_inst_2096_, 2);
lean_inc_ref(v___x_2111_);
v___f_2112_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2112_, 0, v___x_2111_);
lean_closure_set(v___f_2112_, 1, v_inst_2096_);
v___f_2113_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2113_, 0, v___x_2111_);
lean_closure_set(v___f_2113_, 1, v_inst_2096_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___f_2112_);
lean_ctor_set(v___x_2114_, 1, v___f_2113_);
if (lean_obj_tag(v_e_2106_) == 7)
{
lean_object* v_binderName_2115_; lean_object* v_binderType_2116_; lean_object* v_body_2117_; uint8_t v_binderInfo_2118_; lean_object* v_toBind_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_binderName_2115_ = lean_ctor_get(v_e_2106_, 0);
lean_inc(v_binderName_2115_);
v_binderType_2116_ = lean_ctor_get(v_e_2106_, 1);
lean_inc_ref(v_binderType_2116_);
v_body_2117_ = lean_ctor_get(v_e_2106_, 2);
lean_inc_ref(v_body_2117_);
v_binderInfo_2118_ = lean_ctor_get_uint8(v_e_2106_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2106_, 3);
v_toBind_2119_ = lean_ctor_get(v_inst_2094_, 1);
lean_inc(v_toBind_2119_);
v___x_2120_ = lean_box(v_usedLetOnly_2099_);
v___x_2121_ = lean_box(v_skipConstInApp_2100_);
v___x_2122_ = lean_box(v_skipInstances_2101_);
lean_inc(v_x_2104_);
lean_inc(v_postApp_2102_);
lean_inc(v_post_2098_);
lean_inc(v_pre_2097_);
lean_inc_ref(v_inst_2096_);
lean_inc(v_inst_2095_);
lean_inc_ref(v_inst_2094_);
lean_inc_ref(v_fvars_2105_);
v___f_2123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2123_, 0, v_fvars_2105_);
lean_closure_set(v___f_2123_, 1, v_inst_2094_);
lean_closure_set(v___f_2123_, 2, v_inst_2095_);
lean_closure_set(v___f_2123_, 3, v_inst_2096_);
lean_closure_set(v___f_2123_, 4, v_pre_2097_);
lean_closure_set(v___f_2123_, 5, v_post_2098_);
lean_closure_set(v___f_2123_, 6, v___x_2120_);
lean_closure_set(v___f_2123_, 7, v___x_2121_);
lean_closure_set(v___f_2123_, 8, v___x_2122_);
lean_closure_set(v___f_2123_, 9, v_postApp_2102_);
lean_closure_set(v___f_2123_, 10, v_x_2103_);
lean_closure_set(v___f_2123_, 11, v_x_2104_);
lean_closure_set(v___f_2123_, 12, v_body_2117_);
v___x_2124_ = lean_box(v_binderInfo_2118_);
lean_inc(v_a_2107_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2125_, 0, v___x_2114_);
lean_closure_set(v___f_2125_, 1, v___x_2110_);
lean_closure_set(v___f_2125_, 2, v_binderName_2115_);
lean_closure_set(v___f_2125_, 3, v___x_2124_);
lean_closure_set(v___f_2125_, 4, v___f_2123_);
lean_closure_set(v___f_2125_, 5, v_a_2107_);
v___x_2126_ = lean_expr_instantiate_rev(v_binderType_2116_, v_fvars_2105_);
lean_dec_ref(v_fvars_2105_);
lean_dec_ref(v_binderType_2116_);
v___x_2127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2094_, v_inst_2095_, v_inst_2096_, v_pre_2097_, v_post_2098_, v_usedLetOnly_2099_, v_skipConstInApp_2100_, v_skipInstances_2101_, v_postApp_2102_, v_x_2103_, v_x_2104_, v___x_2126_, v_a_2107_);
v___x_2128_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2127_, v___f_2125_);
return v___x_2128_;
}
else
{
lean_object* v_toBind_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2114_, 2);
lean_dec_ref(v___x_2110_);
v_toBind_2129_ = lean_ctor_get(v_inst_2094_, 1);
lean_inc_n(v_toBind_2129_, 2);
v___x_2130_ = lean_box(v_usedLetOnly_2099_);
v___x_2131_ = lean_box(v_skipConstInApp_2100_);
v___x_2132_ = lean_box(v_skipInstances_2101_);
lean_inc(v_a_2107_);
lean_inc(v_x_2104_);
lean_inc(v_postApp_2102_);
lean_inc(v_post_2098_);
lean_inc(v_pre_2097_);
lean_inc_ref(v_inst_2096_);
lean_inc_n(v_inst_2095_, 2);
lean_inc_ref(v_inst_2094_);
v___f_2133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2133_, 0, v_inst_2094_);
lean_closure_set(v___f_2133_, 1, v_inst_2095_);
lean_closure_set(v___f_2133_, 2, v_inst_2096_);
lean_closure_set(v___f_2133_, 3, v_pre_2097_);
lean_closure_set(v___f_2133_, 4, v_post_2098_);
lean_closure_set(v___f_2133_, 5, v___x_2130_);
lean_closure_set(v___f_2133_, 6, v___x_2131_);
lean_closure_set(v___f_2133_, 7, v___x_2132_);
lean_closure_set(v___f_2133_, 8, v_postApp_2102_);
lean_closure_set(v___f_2133_, 9, v_x_2103_);
lean_closure_set(v___f_2133_, 10, v_x_2104_);
lean_closure_set(v___f_2133_, 11, v_a_2107_);
v___x_2134_ = lean_box(v_usedLetOnly_2099_);
lean_inc_ref(v_fvars_2105_);
v___f_2135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2135_, 0, v_fvars_2105_);
lean_closure_set(v___f_2135_, 1, v___x_2134_);
lean_closure_set(v___f_2135_, 2, v_inst_2095_);
lean_closure_set(v___f_2135_, 3, v_toBind_2129_);
lean_closure_set(v___f_2135_, 4, v___f_2133_);
v___x_2136_ = lean_expr_instantiate_rev(v_e_2106_, v_fvars_2105_);
lean_dec_ref(v_fvars_2105_);
lean_dec_ref(v_e_2106_);
v___x_2137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2094_, v_inst_2095_, v_inst_2096_, v_pre_2097_, v_post_2098_, v_usedLetOnly_2099_, v_skipConstInApp_2100_, v_skipInstances_2101_, v_postApp_2102_, v_x_2103_, v_x_2104_, v___x_2136_, v_a_2107_);
v___x_2138_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v___x_2137_, v___f_2135_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_pre_2143_, lean_object* v_post_2144_, uint8_t v_usedLetOnly_2145_, uint8_t v_skipConstInApp_2146_, uint8_t v_skipInstances_2147_, lean_object* v_postApp_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_body_2151_, lean_object* v_x_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_array_push(v_fvars_2139_, v_x_2152_);
v___x_2155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2140_, v_inst_2141_, v_inst_2142_, v_pre_2143_, v_post_2144_, v_usedLetOnly_2145_, v_skipConstInApp_2146_, v_skipInstances_2147_, v_postApp_2148_, v_x_2149_, v_x_2150_, v___x_2154_, v_body_2151_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_pre_2160_, lean_object* v_post_2161_, lean_object* v_usedLetOnly_2162_, lean_object* v_skipConstInApp_2163_, lean_object* v_skipInstances_2164_, lean_object* v_postApp_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_body_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v_usedLetOnly_boxed_2171_; uint8_t v_skipConstInApp_boxed_2172_; uint8_t v_skipInstances_boxed_2173_; lean_object* v_res_2174_; 
v_usedLetOnly_boxed_2171_ = lean_unbox(v_usedLetOnly_2162_);
v_skipConstInApp_boxed_2172_ = lean_unbox(v_skipConstInApp_2163_);
v_skipInstances_boxed_2173_ = lean_unbox(v_skipInstances_2164_);
v_res_2174_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2156_, v_inst_2157_, v_inst_2158_, v_inst_2159_, v_pre_2160_, v_post_2161_, v_usedLetOnly_boxed_2171_, v_skipConstInApp_boxed_2172_, v_skipInstances_boxed_2173_, v_postApp_2165_, v_x_2166_, v_x_2167_, v_body_2168_, v_x_2169_, v___y_2170_);
lean_dec(v___y_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_pre_2178_, lean_object* v_post_2179_, uint8_t v_usedLetOnly_2180_, uint8_t v_skipConstInApp_2181_, uint8_t v_skipInstances_2182_, lean_object* v_postApp_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v_fvars_2186_, lean_object* v_e_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2175_);
v___x_2191_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2184_, v___x_2189_, v___x_2190_, v_inst_2175_);
v___x_2192_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2184_, v___x_2189_, v___x_2190_);
lean_inc_ref_n(v_inst_2177_, 2);
lean_inc_ref(v___x_2192_);
v___f_2193_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2193_, 0, v___x_2192_);
lean_closure_set(v___f_2193_, 1, v_inst_2177_);
v___f_2194_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2194_, 0, v___x_2192_);
lean_closure_set(v___f_2194_, 1, v_inst_2177_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___f_2193_);
lean_ctor_set(v___x_2195_, 1, v___f_2194_);
if (lean_obj_tag(v_e_2187_) == 6)
{
lean_object* v_binderName_2196_; lean_object* v_binderType_2197_; lean_object* v_body_2198_; uint8_t v_binderInfo_2199_; lean_object* v_toBind_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_binderName_2196_ = lean_ctor_get(v_e_2187_, 0);
lean_inc(v_binderName_2196_);
v_binderType_2197_ = lean_ctor_get(v_e_2187_, 1);
lean_inc_ref(v_binderType_2197_);
v_body_2198_ = lean_ctor_get(v_e_2187_, 2);
lean_inc_ref(v_body_2198_);
v_binderInfo_2199_ = lean_ctor_get_uint8(v_e_2187_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2187_, 3);
v_toBind_2200_ = lean_ctor_get(v_inst_2175_, 1);
lean_inc(v_toBind_2200_);
v___x_2201_ = lean_box(v_usedLetOnly_2180_);
v___x_2202_ = lean_box(v_skipConstInApp_2181_);
v___x_2203_ = lean_box(v_skipInstances_2182_);
lean_inc(v_x_2185_);
lean_inc(v_postApp_2183_);
lean_inc(v_post_2179_);
lean_inc(v_pre_2178_);
lean_inc_ref(v_inst_2177_);
lean_inc(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
lean_inc_ref(v_fvars_2186_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2204_, 0, v_fvars_2186_);
lean_closure_set(v___f_2204_, 1, v_inst_2175_);
lean_closure_set(v___f_2204_, 2, v_inst_2176_);
lean_closure_set(v___f_2204_, 3, v_inst_2177_);
lean_closure_set(v___f_2204_, 4, v_pre_2178_);
lean_closure_set(v___f_2204_, 5, v_post_2179_);
lean_closure_set(v___f_2204_, 6, v___x_2201_);
lean_closure_set(v___f_2204_, 7, v___x_2202_);
lean_closure_set(v___f_2204_, 8, v___x_2203_);
lean_closure_set(v___f_2204_, 9, v_postApp_2183_);
lean_closure_set(v___f_2204_, 10, v_x_2184_);
lean_closure_set(v___f_2204_, 11, v_x_2185_);
lean_closure_set(v___f_2204_, 12, v_body_2198_);
v___x_2205_ = lean_box(v_binderInfo_2199_);
lean_inc(v_a_2188_);
v___f_2206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2206_, 0, v___x_2195_);
lean_closure_set(v___f_2206_, 1, v___x_2191_);
lean_closure_set(v___f_2206_, 2, v_binderName_2196_);
lean_closure_set(v___f_2206_, 3, v___x_2205_);
lean_closure_set(v___f_2206_, 4, v___f_2204_);
lean_closure_set(v___f_2206_, 5, v_a_2188_);
v___x_2207_ = lean_expr_instantiate_rev(v_binderType_2197_, v_fvars_2186_);
lean_dec_ref(v_fvars_2186_);
lean_dec_ref(v_binderType_2197_);
v___x_2208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2175_, v_inst_2176_, v_inst_2177_, v_pre_2178_, v_post_2179_, v_usedLetOnly_2180_, v_skipConstInApp_2181_, v_skipInstances_2182_, v_postApp_2183_, v_x_2184_, v_x_2185_, v___x_2207_, v_a_2188_);
v___x_2209_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v___x_2208_, v___f_2206_);
return v___x_2209_;
}
else
{
lean_object* v_toBind_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref_known(v___x_2195_, 2);
lean_dec_ref(v___x_2191_);
v_toBind_2210_ = lean_ctor_get(v_inst_2175_, 1);
lean_inc_n(v_toBind_2210_, 2);
v___x_2211_ = lean_box(v_usedLetOnly_2180_);
v___x_2212_ = lean_box(v_skipConstInApp_2181_);
v___x_2213_ = lean_box(v_skipInstances_2182_);
lean_inc(v_a_2188_);
lean_inc(v_x_2185_);
lean_inc(v_postApp_2183_);
lean_inc(v_post_2179_);
lean_inc(v_pre_2178_);
lean_inc_ref(v_inst_2177_);
lean_inc_n(v_inst_2176_, 2);
lean_inc_ref(v_inst_2175_);
v___f_2214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2214_, 0, v_inst_2175_);
lean_closure_set(v___f_2214_, 1, v_inst_2176_);
lean_closure_set(v___f_2214_, 2, v_inst_2177_);
lean_closure_set(v___f_2214_, 3, v_pre_2178_);
lean_closure_set(v___f_2214_, 4, v_post_2179_);
lean_closure_set(v___f_2214_, 5, v___x_2211_);
lean_closure_set(v___f_2214_, 6, v___x_2212_);
lean_closure_set(v___f_2214_, 7, v___x_2213_);
lean_closure_set(v___f_2214_, 8, v_postApp_2183_);
lean_closure_set(v___f_2214_, 9, v_x_2184_);
lean_closure_set(v___f_2214_, 10, v_x_2185_);
lean_closure_set(v___f_2214_, 11, v_a_2188_);
v___x_2215_ = lean_box(v_usedLetOnly_2180_);
lean_inc_ref(v_fvars_2186_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2216_, 0, v_fvars_2186_);
lean_closure_set(v___f_2216_, 1, v___x_2215_);
lean_closure_set(v___f_2216_, 2, v_inst_2176_);
lean_closure_set(v___f_2216_, 3, v_toBind_2210_);
lean_closure_set(v___f_2216_, 4, v___f_2214_);
v___x_2217_ = lean_expr_instantiate_rev(v_e_2187_, v_fvars_2186_);
lean_dec_ref(v_fvars_2186_);
lean_dec_ref(v_e_2187_);
v___x_2218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2175_, v_inst_2176_, v_inst_2177_, v_pre_2178_, v_post_2179_, v_usedLetOnly_2180_, v_skipConstInApp_2181_, v_skipInstances_2182_, v_postApp_2183_, v_x_2184_, v_x_2185_, v___x_2217_, v_a_2188_);
v___x_2219_ = lean_apply_4(v_toBind_2210_, lean_box(0), lean_box(0), v___x_2218_, v___f_2216_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_pre_2224_, lean_object* v_post_2225_, uint8_t v_usedLetOnly_2226_, uint8_t v_skipConstInApp_2227_, uint8_t v_skipInstances_2228_, lean_object* v_postApp_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_body_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_array_push(v_fvars_2220_, v_x_2233_);
v___x_2236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2221_, v_inst_2222_, v_inst_2223_, v_pre_2224_, v_post_2225_, v_usedLetOnly_2226_, v_skipConstInApp_2227_, v_skipInstances_2228_, v_postApp_2229_, v_x_2230_, v_x_2231_, v___x_2235_, v_body_2232_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_pre_2241_, lean_object* v_post_2242_, lean_object* v_usedLetOnly_2243_, lean_object* v_skipConstInApp_2244_, lean_object* v_skipInstances_2245_, lean_object* v_postApp_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v_body_2249_, lean_object* v_x_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v_usedLetOnly_boxed_2252_; uint8_t v_skipConstInApp_boxed_2253_; uint8_t v_skipInstances_boxed_2254_; lean_object* v_res_2255_; 
v_usedLetOnly_boxed_2252_ = lean_unbox(v_usedLetOnly_2243_);
v_skipConstInApp_boxed_2253_ = lean_unbox(v_skipConstInApp_2244_);
v_skipInstances_boxed_2254_ = lean_unbox(v_skipInstances_2245_);
v_res_2255_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2237_, v_inst_2238_, v_inst_2239_, v_inst_2240_, v_pre_2241_, v_post_2242_, v_usedLetOnly_boxed_2252_, v_skipConstInApp_boxed_2253_, v_skipInstances_boxed_2254_, v_postApp_2246_, v_x_2247_, v_x_2248_, v_body_2249_, v_x_2250_, v___y_2251_);
lean_dec(v___y_2251_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_declName_2258_, lean_object* v___f_2259_, uint8_t v_nondep_2260_, lean_object* v_a_2261_, lean_object* v_value_2262_, lean_object* v_fvars_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_pre_2267_, lean_object* v_post_2268_, uint8_t v_usedLetOnly_2269_, uint8_t v_skipConstInApp_2270_, uint8_t v_skipInstances_2271_, lean_object* v_postApp_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_, lean_object* v_toBind_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2277_ = lean_box(v_nondep_2260_);
lean_inc(v_a_2261_);
v___f_2278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2278_, 0, v___x_2256_);
lean_closure_set(v___f_2278_, 1, v___x_2257_);
lean_closure_set(v___f_2278_, 2, v_declName_2258_);
lean_closure_set(v___f_2278_, 3, v_a_2276_);
lean_closure_set(v___f_2278_, 4, v___f_2259_);
lean_closure_set(v___f_2278_, 5, v___x_2277_);
lean_closure_set(v___f_2278_, 6, v_a_2261_);
v___x_2279_ = lean_expr_instantiate_rev(v_value_2262_, v_fvars_2263_);
v___x_2280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2264_, v_inst_2265_, v_inst_2266_, v_pre_2267_, v_post_2268_, v_usedLetOnly_2269_, v_skipConstInApp_2270_, v_skipInstances_2271_, v_postApp_2272_, v_x_2273_, v_x_2274_, v___x_2279_, v_a_2261_);
v___x_2281_ = lean_apply_4(v_toBind_2275_, lean_box(0), lean_box(0), v___x_2280_, v___f_2278_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2282_ = _args[0];
lean_object* v___x_2283_ = _args[1];
lean_object* v_declName_2284_ = _args[2];
lean_object* v___f_2285_ = _args[3];
lean_object* v_nondep_2286_ = _args[4];
lean_object* v_a_2287_ = _args[5];
lean_object* v_value_2288_ = _args[6];
lean_object* v_fvars_2289_ = _args[7];
lean_object* v_inst_2290_ = _args[8];
lean_object* v_inst_2291_ = _args[9];
lean_object* v_inst_2292_ = _args[10];
lean_object* v_pre_2293_ = _args[11];
lean_object* v_post_2294_ = _args[12];
lean_object* v_usedLetOnly_2295_ = _args[13];
lean_object* v_skipConstInApp_2296_ = _args[14];
lean_object* v_skipInstances_2297_ = _args[15];
lean_object* v_postApp_2298_ = _args[16];
lean_object* v_x_2299_ = _args[17];
lean_object* v_x_2300_ = _args[18];
lean_object* v_toBind_2301_ = _args[19];
lean_object* v_a_2302_ = _args[20];
_start:
{
uint8_t v_nondep_3862__boxed_2303_; uint8_t v_usedLetOnly_boxed_2304_; uint8_t v_skipConstInApp_boxed_2305_; uint8_t v_skipInstances_boxed_2306_; lean_object* v_res_2307_; 
v_nondep_3862__boxed_2303_ = lean_unbox(v_nondep_2286_);
v_usedLetOnly_boxed_2304_ = lean_unbox(v_usedLetOnly_2295_);
v_skipConstInApp_boxed_2305_ = lean_unbox(v_skipConstInApp_2296_);
v_skipInstances_boxed_2306_ = lean_unbox(v_skipInstances_2297_);
v_res_2307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2282_, v___x_2283_, v_declName_2284_, v___f_2285_, v_nondep_3862__boxed_2303_, v_a_2287_, v_value_2288_, v_fvars_2289_, v_inst_2290_, v_inst_2291_, v_inst_2292_, v_pre_2293_, v_post_2294_, v_usedLetOnly_boxed_2304_, v_skipConstInApp_boxed_2305_, v_skipInstances_boxed_2306_, v_postApp_2298_, v_x_2299_, v_x_2300_, v_toBind_2301_, v_a_2302_);
lean_dec_ref(v_fvars_2289_);
lean_dec_ref(v_value_2288_);
lean_dec(v_a_2287_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_pre_2311_, lean_object* v_post_2312_, uint8_t v_usedLetOnly_2313_, uint8_t v_skipConstInApp_2314_, uint8_t v_skipInstances_2315_, lean_object* v_postApp_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_, lean_object* v_fvars_2319_, lean_object* v_e_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___f_2326_; lean_object* v___f_2327_; lean_object* v___x_2328_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2323_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2308_);
v___x_2324_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2317_, v___x_2322_, v___x_2323_, v_inst_2308_);
v___x_2325_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2317_, v___x_2322_, v___x_2323_);
lean_inc_ref_n(v_inst_2310_, 2);
lean_inc_ref(v___x_2325_);
v___f_2326_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2326_, 0, v___x_2325_);
lean_closure_set(v___f_2326_, 1, v_inst_2310_);
v___f_2327_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2327_, 0, v___x_2325_);
lean_closure_set(v___f_2327_, 1, v_inst_2310_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___f_2326_);
lean_ctor_set(v___x_2328_, 1, v___f_2327_);
if (lean_obj_tag(v_e_2320_) == 8)
{
lean_object* v_declName_2329_; lean_object* v_type_2330_; lean_object* v_value_2331_; lean_object* v_body_2332_; uint8_t v_nondep_2333_; lean_object* v_toBind_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___f_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_declName_2329_ = lean_ctor_get(v_e_2320_, 0);
lean_inc(v_declName_2329_);
v_type_2330_ = lean_ctor_get(v_e_2320_, 1);
lean_inc_ref(v_type_2330_);
v_value_2331_ = lean_ctor_get(v_e_2320_, 2);
lean_inc_ref(v_value_2331_);
v_body_2332_ = lean_ctor_get(v_e_2320_, 3);
lean_inc_ref(v_body_2332_);
v_nondep_2333_ = lean_ctor_get_uint8(v_e_2320_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2320_, 4);
v_toBind_2334_ = lean_ctor_get(v_inst_2308_, 1);
lean_inc_n(v_toBind_2334_, 2);
v___x_2335_ = lean_box(v_usedLetOnly_2313_);
v___x_2336_ = lean_box(v_skipConstInApp_2314_);
v___x_2337_ = lean_box(v_skipInstances_2315_);
lean_inc_n(v_x_2318_, 2);
lean_inc_n(v_postApp_2316_, 2);
lean_inc_n(v_post_2312_, 2);
lean_inc_n(v_pre_2311_, 2);
lean_inc_ref_n(v_inst_2310_, 2);
lean_inc_n(v_inst_2309_, 2);
lean_inc_ref_n(v_inst_2308_, 2);
lean_inc_ref_n(v_fvars_2319_, 2);
v___f_2338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_2338_, 0, v_fvars_2319_);
lean_closure_set(v___f_2338_, 1, v_inst_2308_);
lean_closure_set(v___f_2338_, 2, v_inst_2309_);
lean_closure_set(v___f_2338_, 3, v_inst_2310_);
lean_closure_set(v___f_2338_, 4, v_pre_2311_);
lean_closure_set(v___f_2338_, 5, v_post_2312_);
lean_closure_set(v___f_2338_, 6, v___x_2335_);
lean_closure_set(v___f_2338_, 7, v___x_2336_);
lean_closure_set(v___f_2338_, 8, v___x_2337_);
lean_closure_set(v___f_2338_, 9, v_postApp_2316_);
lean_closure_set(v___f_2338_, 10, v_x_2317_);
lean_closure_set(v___f_2338_, 11, v_x_2318_);
lean_closure_set(v___f_2338_, 12, v_body_2332_);
v___x_2339_ = lean_box(v_nondep_2333_);
v___x_2340_ = lean_box(v_usedLetOnly_2313_);
v___x_2341_ = lean_box(v_skipConstInApp_2314_);
v___x_2342_ = lean_box(v_skipInstances_2315_);
lean_inc(v_a_2321_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 21, 20);
lean_closure_set(v___f_2343_, 0, v___x_2328_);
lean_closure_set(v___f_2343_, 1, v___x_2324_);
lean_closure_set(v___f_2343_, 2, v_declName_2329_);
lean_closure_set(v___f_2343_, 3, v___f_2338_);
lean_closure_set(v___f_2343_, 4, v___x_2339_);
lean_closure_set(v___f_2343_, 5, v_a_2321_);
lean_closure_set(v___f_2343_, 6, v_value_2331_);
lean_closure_set(v___f_2343_, 7, v_fvars_2319_);
lean_closure_set(v___f_2343_, 8, v_inst_2308_);
lean_closure_set(v___f_2343_, 9, v_inst_2309_);
lean_closure_set(v___f_2343_, 10, v_inst_2310_);
lean_closure_set(v___f_2343_, 11, v_pre_2311_);
lean_closure_set(v___f_2343_, 12, v_post_2312_);
lean_closure_set(v___f_2343_, 13, v___x_2340_);
lean_closure_set(v___f_2343_, 14, v___x_2341_);
lean_closure_set(v___f_2343_, 15, v___x_2342_);
lean_closure_set(v___f_2343_, 16, v_postApp_2316_);
lean_closure_set(v___f_2343_, 17, v_x_2317_);
lean_closure_set(v___f_2343_, 18, v_x_2318_);
lean_closure_set(v___f_2343_, 19, v_toBind_2334_);
v___x_2344_ = lean_expr_instantiate_rev(v_type_2330_, v_fvars_2319_);
lean_dec_ref(v_fvars_2319_);
lean_dec_ref(v_type_2330_);
v___x_2345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2308_, v_inst_2309_, v_inst_2310_, v_pre_2311_, v_post_2312_, v_usedLetOnly_2313_, v_skipConstInApp_2314_, v_skipInstances_2315_, v_postApp_2316_, v_x_2317_, v_x_2318_, v___x_2344_, v_a_2321_);
v___x_2346_ = lean_apply_4(v_toBind_2334_, lean_box(0), lean_box(0), v___x_2345_, v___f_2343_);
return v___x_2346_;
}
else
{
lean_object* v_toBind_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref_known(v___x_2328_, 2);
lean_dec_ref(v___x_2324_);
v_toBind_2347_ = lean_ctor_get(v_inst_2308_, 1);
lean_inc_n(v_toBind_2347_, 2);
v___x_2348_ = lean_box(v_usedLetOnly_2313_);
v___x_2349_ = lean_box(v_skipConstInApp_2314_);
v___x_2350_ = lean_box(v_skipInstances_2315_);
lean_inc(v_a_2321_);
lean_inc(v_x_2318_);
lean_inc(v_postApp_2316_);
lean_inc(v_post_2312_);
lean_inc(v_pre_2311_);
lean_inc_ref(v_inst_2310_);
lean_inc_n(v_inst_2309_, 2);
lean_inc_ref(v_inst_2308_);
v___f_2351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_2351_, 0, v_inst_2308_);
lean_closure_set(v___f_2351_, 1, v_inst_2309_);
lean_closure_set(v___f_2351_, 2, v_inst_2310_);
lean_closure_set(v___f_2351_, 3, v_pre_2311_);
lean_closure_set(v___f_2351_, 4, v_post_2312_);
lean_closure_set(v___f_2351_, 5, v___x_2348_);
lean_closure_set(v___f_2351_, 6, v___x_2349_);
lean_closure_set(v___f_2351_, 7, v___x_2350_);
lean_closure_set(v___f_2351_, 8, v_postApp_2316_);
lean_closure_set(v___f_2351_, 9, v_x_2317_);
lean_closure_set(v___f_2351_, 10, v_x_2318_);
lean_closure_set(v___f_2351_, 11, v_a_2321_);
v___x_2352_ = lean_box(v_usedLetOnly_2313_);
lean_inc_ref(v_fvars_2319_);
v___f_2353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2353_, 0, v_fvars_2319_);
lean_closure_set(v___f_2353_, 1, v___x_2352_);
lean_closure_set(v___f_2353_, 2, v_inst_2309_);
lean_closure_set(v___f_2353_, 3, v_toBind_2347_);
lean_closure_set(v___f_2353_, 4, v___f_2351_);
v___x_2354_ = lean_expr_instantiate_rev(v_e_2320_, v_fvars_2319_);
lean_dec_ref(v_fvars_2319_);
lean_dec_ref(v_e_2320_);
v___x_2355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2308_, v_inst_2309_, v_inst_2310_, v_pre_2311_, v_post_2312_, v_usedLetOnly_2313_, v_skipConstInApp_2314_, v_skipInstances_2315_, v_postApp_2316_, v_x_2317_, v_x_2318_, v___x_2354_, v_a_2321_);
v___x_2356_ = lean_apply_4(v_toBind_2347_, lean_box(0), lean_box(0), v___x_2355_, v___f_2353_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_pre_2360_, lean_object* v_post_2361_, lean_object* v_usedLetOnly_2362_, lean_object* v_skipConstInApp_2363_, lean_object* v_skipInstances_2364_, lean_object* v_postApp_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v___y_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v_usedLetOnly_boxed_2370_; uint8_t v_skipConstInApp_boxed_2371_; uint8_t v_skipInstances_boxed_2372_; lean_object* v_res_2373_; 
v_usedLetOnly_boxed_2370_ = lean_unbox(v_usedLetOnly_2362_);
v_skipConstInApp_boxed_2371_ = lean_unbox(v_skipConstInApp_2363_);
v_skipInstances_boxed_2372_ = lean_unbox(v_skipInstances_2364_);
v_res_2373_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_inst_2357_, v_inst_2358_, v_inst_2359_, v_pre_2360_, v_post_2361_, v_usedLetOnly_boxed_2370_, v_skipConstInApp_boxed_2371_, v_skipInstances_boxed_2372_, v_postApp_2365_, v_x_2366_, v_x_2367_, v___y_2368_, v_a_2369_);
lean_dec(v___y_2368_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_pre_2377_, lean_object* v_post_2378_, lean_object* v_usedLetOnly_2379_, lean_object* v_skipConstInApp_2380_, lean_object* v_skipInstances_2381_, lean_object* v_postApp_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_e_2385_, lean_object* v_a_2386_){
_start:
{
uint8_t v_usedLetOnly_boxed_2387_; uint8_t v_skipConstInApp_boxed_2388_; uint8_t v_skipInstances_boxed_2389_; lean_object* v_res_2390_; 
v_usedLetOnly_boxed_2387_ = lean_unbox(v_usedLetOnly_2379_);
v_skipConstInApp_boxed_2388_ = lean_unbox(v_skipConstInApp_2380_);
v_skipInstances_boxed_2389_ = lean_unbox(v_skipInstances_2381_);
v_res_2390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2374_, v_inst_2375_, v_inst_2376_, v_pre_2377_, v_post_2378_, v_usedLetOnly_boxed_2387_, v_skipConstInApp_boxed_2388_, v_skipInstances_boxed_2389_, v_postApp_2382_, v_x_2383_, v_x_2384_, v_e_2385_, v_a_2386_);
lean_dec(v_a_2386_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(lean_object* v___x_2391_, lean_object* v_toApplicative_2392_, lean_object* v_toBind_2393_, lean_object* v___f_2394_, lean_object* v_paramInfo_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_pre_2399_, lean_object* v_post_2400_, uint8_t v_usedLetOnly_2401_, uint8_t v_skipConstInApp_2402_, uint8_t v_skipInstances_2403_, lean_object* v_postApp_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_next_2407_, lean_object* v_acc_2408_, lean_object* v_h_2409_, lean_object* v_G_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_nat_dec_lt(v_next_2407_, v___x_2391_);
if (v___x_2412_ == 0)
{
lean_object* v_toPure_2413_; lean_object* v___x_2414_; 
lean_dec(v_G_2410_);
lean_dec(v_next_2407_);
lean_dec(v_x_2406_);
lean_dec(v_postApp_2404_);
lean_dec(v_post_2400_);
lean_dec(v_pre_2399_);
lean_dec_ref(v_inst_2398_);
lean_dec(v_inst_2397_);
lean_dec_ref(v_inst_2396_);
lean_dec(v___f_2394_);
lean_dec(v_toBind_2393_);
v_toPure_2413_ = lean_ctor_get(v_toApplicative_2392_, 1);
lean_inc(v_toPure_2413_);
lean_dec_ref(v_toApplicative_2392_);
v___x_2414_ = lean_apply_2(v_toPure_2413_, lean_box(0), v_acc_2408_);
return v___x_2414_;
}
else
{
lean_object* v___f_2415_; lean_object* v___y_2417_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
lean_inc(v___y_2411_);
lean_inc(v_next_2407_);
lean_inc_ref(v_toApplicative_2392_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_2415_, 0, v_toApplicative_2392_);
lean_closure_set(v___f_2415_, 1, v_next_2407_);
lean_closure_set(v___f_2415_, 2, v_G_2410_);
lean_closure_set(v___f_2415_, 3, v___y_2411_);
v___x_2420_ = lean_array_fget_borrowed(v_acc_2408_, v_next_2407_);
v___x_2421_ = lean_array_get_size(v_paramInfo_2395_);
v___x_2422_ = lean_nat_dec_lt(v_next_2407_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___f_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_inc(v___x_2420_);
v___f_2423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2423_, 0, v_toApplicative_2392_);
lean_closure_set(v___f_2423_, 1, v_acc_2408_);
lean_closure_set(v___f_2423_, 2, v_next_2407_);
v___x_2424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2396_, v_inst_2397_, v_inst_2398_, v_pre_2399_, v_post_2400_, v_usedLetOnly_2401_, v_skipConstInApp_2402_, v_skipInstances_2403_, v_postApp_2404_, v_x_2405_, v_x_2406_, v___x_2420_, v___y_2411_);
lean_inc(v_toBind_2393_);
v___x_2425_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v___x_2424_, v___f_2423_);
v___y_2417_ = v___x_2425_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2426_; uint8_t v_isInstance_2427_; 
v___x_2426_ = lean_array_fget_borrowed(v_paramInfo_2395_, v_next_2407_);
v_isInstance_2427_ = lean_ctor_get_uint8(v___x_2426_, sizeof(void*)*1 + 4);
if (v_isInstance_2427_ == 0)
{
lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_inc(v___x_2420_);
v___f_2428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2428_, 0, v_toApplicative_2392_);
lean_closure_set(v___f_2428_, 1, v_acc_2408_);
lean_closure_set(v___f_2428_, 2, v_next_2407_);
v___x_2429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2396_, v_inst_2397_, v_inst_2398_, v_pre_2399_, v_post_2400_, v_usedLetOnly_2401_, v_skipConstInApp_2402_, v_skipInstances_2403_, v_postApp_2404_, v_x_2405_, v_x_2406_, v___x_2420_, v___y_2411_);
lean_inc(v_toBind_2393_);
v___x_2430_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v___x_2429_, v___f_2428_);
v___y_2417_ = v___x_2430_;
goto v___jp_2416_;
}
else
{
lean_object* v_toPure_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec(v_next_2407_);
lean_dec(v_x_2406_);
lean_dec(v_postApp_2404_);
lean_dec(v_post_2400_);
lean_dec(v_pre_2399_);
lean_dec_ref(v_inst_2398_);
lean_dec(v_inst_2397_);
lean_dec_ref(v_inst_2396_);
v_toPure_2431_ = lean_ctor_get(v_toApplicative_2392_, 1);
lean_inc(v_toPure_2431_);
lean_dec_ref(v_toApplicative_2392_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_acc_2408_);
v___x_2433_ = lean_apply_2(v_toPure_2431_, lean_box(0), v___x_2432_);
v___y_2417_ = v___x_2433_;
goto v___jp_2416_;
}
}
v___jp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_inc(v_toBind_2393_);
v___x_2418_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v___y_2417_, v___f_2394_);
v___x_2419_ = lean_apply_4(v_toBind_2393_, lean_box(0), lean_box(0), v___x_2418_, v___f_2415_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_2434_ = _args[0];
lean_object* v_toApplicative_2435_ = _args[1];
lean_object* v_toBind_2436_ = _args[2];
lean_object* v___f_2437_ = _args[3];
lean_object* v_paramInfo_2438_ = _args[4];
lean_object* v_inst_2439_ = _args[5];
lean_object* v_inst_2440_ = _args[6];
lean_object* v_inst_2441_ = _args[7];
lean_object* v_pre_2442_ = _args[8];
lean_object* v_post_2443_ = _args[9];
lean_object* v_usedLetOnly_2444_ = _args[10];
lean_object* v_skipConstInApp_2445_ = _args[11];
lean_object* v_skipInstances_2446_ = _args[12];
lean_object* v_postApp_2447_ = _args[13];
lean_object* v_x_2448_ = _args[14];
lean_object* v_x_2449_ = _args[15];
lean_object* v_next_2450_ = _args[16];
lean_object* v_acc_2451_ = _args[17];
lean_object* v_h_2452_ = _args[18];
lean_object* v_G_2453_ = _args[19];
lean_object* v___y_2454_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_2455_; uint8_t v_skipConstInApp_boxed_2456_; uint8_t v_skipInstances_boxed_2457_; lean_object* v_res_2458_; 
v_usedLetOnly_boxed_2455_ = lean_unbox(v_usedLetOnly_2444_);
v_skipConstInApp_boxed_2456_ = lean_unbox(v_skipConstInApp_2445_);
v_skipInstances_boxed_2457_ = lean_unbox(v_skipInstances_2446_);
v_res_2458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v___x_2434_, v_toApplicative_2435_, v_toBind_2436_, v___f_2437_, v_paramInfo_2438_, v_inst_2439_, v_inst_2440_, v_inst_2441_, v_pre_2442_, v_post_2443_, v_usedLetOnly_boxed_2455_, v_skipConstInApp_boxed_2456_, v_skipInstances_boxed_2457_, v_postApp_2447_, v_x_2448_, v_x_2449_, v_next_2450_, v_acc_2451_, v_h_2452_, v_G_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v_paramInfo_2438_);
lean_dec(v___x_2434_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2459_, lean_object* v_toApplicative_2460_, lean_object* v_toBind_2461_, lean_object* v___f_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_pre_2466_, lean_object* v_post_2467_, uint8_t v_usedLetOnly_2468_, uint8_t v_skipConstInApp_2469_, uint8_t v_skipInstances_2470_, lean_object* v_postApp_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_, lean_object* v_args_2474_, lean_object* v___y_2475_, lean_object* v___f_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_paramInfo_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___f_2483_; lean_object* v___x_3272__overap_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_paramInfo_2478_ = lean_ctor_get(v_a_2477_, 0);
lean_inc_ref(v_paramInfo_2478_);
lean_dec_ref(v_a_2477_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_box(v_usedLetOnly_2468_);
v___x_2481_ = lean_box(v_skipConstInApp_2469_);
v___x_2482_ = lean_box(v_skipInstances_2470_);
lean_inc(v_toBind_2461_);
v___f_2483_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 21, 16);
lean_closure_set(v___f_2483_, 0, v___x_2459_);
lean_closure_set(v___f_2483_, 1, v_toApplicative_2460_);
lean_closure_set(v___f_2483_, 2, v_toBind_2461_);
lean_closure_set(v___f_2483_, 3, v___f_2462_);
lean_closure_set(v___f_2483_, 4, v_paramInfo_2478_);
lean_closure_set(v___f_2483_, 5, v_inst_2463_);
lean_closure_set(v___f_2483_, 6, v_inst_2464_);
lean_closure_set(v___f_2483_, 7, v_inst_2465_);
lean_closure_set(v___f_2483_, 8, v_pre_2466_);
lean_closure_set(v___f_2483_, 9, v_post_2467_);
lean_closure_set(v___f_2483_, 10, v___x_2480_);
lean_closure_set(v___f_2483_, 11, v___x_2481_);
lean_closure_set(v___f_2483_, 12, v___x_2482_);
lean_closure_set(v___f_2483_, 13, v_postApp_2471_);
lean_closure_set(v___f_2483_, 14, v_x_2472_);
lean_closure_set(v___f_2483_, 15, v_x_2473_);
v___x_3272__overap_2484_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2483_, v___x_2479_, v_args_2474_, lean_box(0));
lean_inc(v___y_2475_);
v___x_2485_ = lean_apply_1(v___x_3272__overap_2484_, v___y_2475_);
v___x_2486_ = lean_apply_4(v_toBind_2461_, lean_box(0), lean_box(0), v___x_2485_, v___f_2476_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2487_ = _args[0];
lean_object* v_toApplicative_2488_ = _args[1];
lean_object* v_toBind_2489_ = _args[2];
lean_object* v___f_2490_ = _args[3];
lean_object* v_inst_2491_ = _args[4];
lean_object* v_inst_2492_ = _args[5];
lean_object* v_inst_2493_ = _args[6];
lean_object* v_pre_2494_ = _args[7];
lean_object* v_post_2495_ = _args[8];
lean_object* v_usedLetOnly_2496_ = _args[9];
lean_object* v_skipConstInApp_2497_ = _args[10];
lean_object* v_skipInstances_2498_ = _args[11];
lean_object* v_postApp_2499_ = _args[12];
lean_object* v_x_2500_ = _args[13];
lean_object* v_x_2501_ = _args[14];
lean_object* v_args_2502_ = _args[15];
lean_object* v___y_2503_ = _args[16];
lean_object* v___f_2504_ = _args[17];
lean_object* v_a_2505_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_2506_; uint8_t v_skipConstInApp_boxed_2507_; uint8_t v_skipInstances_boxed_2508_; lean_object* v_res_2509_; 
v_usedLetOnly_boxed_2506_ = lean_unbox(v_usedLetOnly_2496_);
v_skipConstInApp_boxed_2507_ = lean_unbox(v_skipConstInApp_2497_);
v_skipInstances_boxed_2508_ = lean_unbox(v_skipInstances_2498_);
v_res_2509_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2487_, v_toApplicative_2488_, v_toBind_2489_, v___f_2490_, v_inst_2491_, v_inst_2492_, v_inst_2493_, v_pre_2494_, v_post_2495_, v_usedLetOnly_boxed_2506_, v_skipConstInApp_boxed_2507_, v_skipInstances_boxed_2508_, v_postApp_2499_, v_x_2500_, v_x_2501_, v_args_2502_, v___y_2503_, v___f_2504_, v_a_2505_);
lean_dec(v___y_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(uint8_t v_skipInstances_2510_, lean_object* v_inst_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_pre_2514_, lean_object* v_post_2515_, uint8_t v_usedLetOnly_2516_, uint8_t v_skipConstInApp_2517_, lean_object* v_postApp_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_, lean_object* v_toBind_2522_, lean_object* v_args_2523_, lean_object* v___x_2524_, lean_object* v_toApplicative_2525_, lean_object* v___f_2526_, lean_object* v_f_2527_, lean_object* v___y_2528_){
_start:
{
if (v_skipInstances_2510_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; size_t v_sz_2538_; size_t v___x_2539_; lean_object* v___x_3287__overap_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v___f_2526_);
lean_dec_ref(v_toApplicative_2525_);
v___x_2529_ = lean_box(v_usedLetOnly_2516_);
v___x_2530_ = lean_box(v_skipConstInApp_2517_);
v___x_2531_ = lean_box(v_skipInstances_2510_);
lean_inc_n(v___y_2528_, 2);
lean_inc(v_x_2520_);
lean_inc_n(v_postApp_2518_, 2);
lean_inc(v_post_2515_);
lean_inc(v_pre_2514_);
lean_inc_ref(v_inst_2513_);
lean_inc(v_inst_2512_);
lean_inc_ref(v_inst_2511_);
v___f_2532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2532_, 0, v_inst_2511_);
lean_closure_set(v___f_2532_, 1, v_inst_2512_);
lean_closure_set(v___f_2532_, 2, v_inst_2513_);
lean_closure_set(v___f_2532_, 3, v_pre_2514_);
lean_closure_set(v___f_2532_, 4, v_post_2515_);
lean_closure_set(v___f_2532_, 5, v___x_2529_);
lean_closure_set(v___f_2532_, 6, v___x_2530_);
lean_closure_set(v___f_2532_, 7, v___x_2531_);
lean_closure_set(v___f_2532_, 8, v_postApp_2518_);
lean_closure_set(v___f_2532_, 9, v_x_2519_);
lean_closure_set(v___f_2532_, 10, v_x_2520_);
lean_closure_set(v___f_2532_, 11, v___y_2528_);
lean_inc(v_toBind_2522_);
v___f_2533_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2533_, 0, v_f_2527_);
lean_closure_set(v___f_2533_, 1, v_postApp_2518_);
lean_closure_set(v___f_2533_, 2, v___y_2521_);
lean_closure_set(v___f_2533_, 3, v_toBind_2522_);
lean_closure_set(v___f_2533_, 4, v___f_2532_);
v___x_2534_ = lean_box(v_usedLetOnly_2516_);
v___x_2535_ = lean_box(v_skipConstInApp_2517_);
v___x_2536_ = lean_box(v_skipInstances_2510_);
v___x_2537_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 13, 11);
lean_closure_set(v___x_2537_, 0, v_inst_2511_);
lean_closure_set(v___x_2537_, 1, v_inst_2512_);
lean_closure_set(v___x_2537_, 2, v_inst_2513_);
lean_closure_set(v___x_2537_, 3, v_pre_2514_);
lean_closure_set(v___x_2537_, 4, v_post_2515_);
lean_closure_set(v___x_2537_, 5, v___x_2534_);
lean_closure_set(v___x_2537_, 6, v___x_2535_);
lean_closure_set(v___x_2537_, 7, v___x_2536_);
lean_closure_set(v___x_2537_, 8, v_postApp_2518_);
lean_closure_set(v___x_2537_, 9, v_x_2519_);
lean_closure_set(v___x_2537_, 10, v_x_2520_);
v_sz_2538_ = lean_array_size(v_args_2523_);
v___x_2539_ = ((size_t)0ULL);
v___x_3287__overap_2540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2524_, v___x_2537_, v_sz_2538_, v___x_2539_, v_args_2523_);
v___x_2541_ = lean_apply_1(v___x_3287__overap_2540_, v___y_2528_);
v___x_2542_ = lean_apply_4(v_toBind_2522_, lean_box(0), lean_box(0), v___x_2541_, v___f_2533_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec_ref(v___x_2524_);
v___x_2543_ = lean_box(v_usedLetOnly_2516_);
v___x_2544_ = lean_box(v_skipConstInApp_2517_);
v___x_2545_ = lean_box(v_skipInstances_2510_);
lean_inc_n(v___y_2528_, 2);
lean_inc(v_x_2520_);
lean_inc_n(v_postApp_2518_, 2);
lean_inc(v_post_2515_);
lean_inc(v_pre_2514_);
lean_inc_ref(v_inst_2513_);
lean_inc_n(v_inst_2512_, 2);
lean_inc_ref(v_inst_2511_);
v___f_2546_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2546_, 0, v_inst_2511_);
lean_closure_set(v___f_2546_, 1, v_inst_2512_);
lean_closure_set(v___f_2546_, 2, v_inst_2513_);
lean_closure_set(v___f_2546_, 3, v_pre_2514_);
lean_closure_set(v___f_2546_, 4, v_post_2515_);
lean_closure_set(v___f_2546_, 5, v___x_2543_);
lean_closure_set(v___f_2546_, 6, v___x_2544_);
lean_closure_set(v___f_2546_, 7, v___x_2545_);
lean_closure_set(v___f_2546_, 8, v_postApp_2518_);
lean_closure_set(v___f_2546_, 9, v_x_2519_);
lean_closure_set(v___f_2546_, 10, v_x_2520_);
lean_closure_set(v___f_2546_, 11, v___y_2528_);
lean_inc_n(v_toBind_2522_, 2);
lean_inc_ref(v_f_2527_);
v___f_2547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2547_, 0, v_f_2527_);
lean_closure_set(v___f_2547_, 1, v_postApp_2518_);
lean_closure_set(v___f_2547_, 2, v___y_2521_);
lean_closure_set(v___f_2547_, 3, v_toBind_2522_);
lean_closure_set(v___f_2547_, 4, v___f_2546_);
v___x_2548_ = lean_array_get_size(v_args_2523_);
v___x_2549_ = lean_box(v_usedLetOnly_2516_);
v___x_2550_ = lean_box(v_skipConstInApp_2517_);
v___x_2551_ = lean_box(v_skipInstances_2510_);
v___f_2552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 19, 18);
lean_closure_set(v___f_2552_, 0, v___x_2548_);
lean_closure_set(v___f_2552_, 1, v_toApplicative_2525_);
lean_closure_set(v___f_2552_, 2, v_toBind_2522_);
lean_closure_set(v___f_2552_, 3, v___f_2526_);
lean_closure_set(v___f_2552_, 4, v_inst_2511_);
lean_closure_set(v___f_2552_, 5, v_inst_2512_);
lean_closure_set(v___f_2552_, 6, v_inst_2513_);
lean_closure_set(v___f_2552_, 7, v_pre_2514_);
lean_closure_set(v___f_2552_, 8, v_post_2515_);
lean_closure_set(v___f_2552_, 9, v___x_2549_);
lean_closure_set(v___f_2552_, 10, v___x_2550_);
lean_closure_set(v___f_2552_, 11, v___x_2551_);
lean_closure_set(v___f_2552_, 12, v_postApp_2518_);
lean_closure_set(v___f_2552_, 13, v_x_2519_);
lean_closure_set(v___f_2552_, 14, v_x_2520_);
lean_closure_set(v___f_2552_, 15, v_args_2523_);
lean_closure_set(v___f_2552_, 16, v___y_2528_);
lean_closure_set(v___f_2552_, 17, v___f_2547_);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2553_, 0, v_f_2527_);
lean_closure_set(v___x_2553_, 1, v___x_2548_);
v___x_2554_ = lean_apply_2(v_inst_2512_, lean_box(0), v___x_2553_);
v___x_2555_ = lean_apply_4(v_toBind_2522_, lean_box(0), lean_box(0), v___x_2554_, v___f_2552_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_skipInstances_2556_ = _args[0];
lean_object* v_inst_2557_ = _args[1];
lean_object* v_inst_2558_ = _args[2];
lean_object* v_inst_2559_ = _args[3];
lean_object* v_pre_2560_ = _args[4];
lean_object* v_post_2561_ = _args[5];
lean_object* v_usedLetOnly_2562_ = _args[6];
lean_object* v_skipConstInApp_2563_ = _args[7];
lean_object* v_postApp_2564_ = _args[8];
lean_object* v_x_2565_ = _args[9];
lean_object* v_x_2566_ = _args[10];
lean_object* v___y_2567_ = _args[11];
lean_object* v_toBind_2568_ = _args[12];
lean_object* v_args_2569_ = _args[13];
lean_object* v___x_2570_ = _args[14];
lean_object* v_toApplicative_2571_ = _args[15];
lean_object* v___f_2572_ = _args[16];
lean_object* v_f_2573_ = _args[17];
lean_object* v___y_2574_ = _args[18];
_start:
{
uint8_t v_skipInstances_boxed_2575_; uint8_t v_usedLetOnly_boxed_2576_; uint8_t v_skipConstInApp_boxed_2577_; lean_object* v_res_2578_; 
v_skipInstances_boxed_2575_ = lean_unbox(v_skipInstances_2556_);
v_usedLetOnly_boxed_2576_ = lean_unbox(v_usedLetOnly_2562_);
v_skipConstInApp_boxed_2577_ = lean_unbox(v_skipConstInApp_2563_);
v_res_2578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v_skipInstances_boxed_2575_, v_inst_2557_, v_inst_2558_, v_inst_2559_, v_pre_2560_, v_post_2561_, v_usedLetOnly_boxed_2576_, v_skipConstInApp_boxed_2577_, v_postApp_2564_, v_x_2565_, v_x_2566_, v___y_2567_, v_toBind_2568_, v_args_2569_, v___x_2570_, v_toApplicative_2571_, v___f_2572_, v_f_2573_, v___y_2574_);
lean_dec(v___y_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(uint8_t v_skipInstances_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_pre_2583_, lean_object* v_post_2584_, uint8_t v_usedLetOnly_2585_, uint8_t v_skipConstInApp_2586_, lean_object* v_postApp_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v_toBind_2591_, lean_object* v___x_2592_, lean_object* v_toApplicative_2593_, lean_object* v___f_2594_, lean_object* v_f_2595_, lean_object* v_args_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; 
v___x_2598_ = lean_box(v_skipInstances_2579_);
v___x_2599_ = lean_box(v_usedLetOnly_2585_);
v___x_2600_ = lean_box(v_skipConstInApp_2586_);
lean_inc_ref(v_toApplicative_2593_);
lean_inc(v_toBind_2591_);
lean_inc(v_x_2589_);
lean_inc(v_postApp_2587_);
lean_inc(v_post_2584_);
lean_inc(v_pre_2583_);
lean_inc_ref(v_inst_2582_);
lean_inc(v_inst_2581_);
lean_inc_ref(v_inst_2580_);
v___f_2601_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 19, 17);
lean_closure_set(v___f_2601_, 0, v___x_2598_);
lean_closure_set(v___f_2601_, 1, v_inst_2580_);
lean_closure_set(v___f_2601_, 2, v_inst_2581_);
lean_closure_set(v___f_2601_, 3, v_inst_2582_);
lean_closure_set(v___f_2601_, 4, v_pre_2583_);
lean_closure_set(v___f_2601_, 5, v_post_2584_);
lean_closure_set(v___f_2601_, 6, v___x_2599_);
lean_closure_set(v___f_2601_, 7, v___x_2600_);
lean_closure_set(v___f_2601_, 8, v_postApp_2587_);
lean_closure_set(v___f_2601_, 9, v_x_2588_);
lean_closure_set(v___f_2601_, 10, v_x_2589_);
lean_closure_set(v___f_2601_, 11, v___y_2590_);
lean_closure_set(v___f_2601_, 12, v_toBind_2591_);
lean_closure_set(v___f_2601_, 13, v_args_2596_);
lean_closure_set(v___f_2601_, 14, v___x_2592_);
lean_closure_set(v___f_2601_, 15, v_toApplicative_2593_);
lean_closure_set(v___f_2601_, 16, v___f_2594_);
lean_inc(v___y_2597_);
v___f_2602_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2602_, 0, v___f_2601_);
lean_closure_set(v___f_2602_, 1, v___y_2597_);
if (v_skipConstInApp_2586_ == 0)
{
lean_dec_ref(v_toApplicative_2593_);
goto v___jp_2603_;
}
else
{
uint8_t v___x_2606_; 
v___x_2606_ = l_Lean_Expr_isConst(v_f_2595_);
if (v___x_2606_ == 0)
{
lean_dec_ref(v_toApplicative_2593_);
goto v___jp_2603_;
}
else
{
lean_object* v_toPure_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec(v_x_2589_);
lean_dec(v_postApp_2587_);
lean_dec(v_post_2584_);
lean_dec(v_pre_2583_);
lean_dec_ref(v_inst_2582_);
lean_dec(v_inst_2581_);
lean_dec_ref(v_inst_2580_);
v_toPure_2607_ = lean_ctor_get(v_toApplicative_2593_, 1);
lean_inc(v_toPure_2607_);
lean_dec_ref(v_toApplicative_2593_);
v___x_2608_ = lean_apply_2(v_toPure_2607_, lean_box(0), v_f_2595_);
v___x_2609_ = lean_apply_4(v_toBind_2591_, lean_box(0), lean_box(0), v___x_2608_, v___f_2602_);
return v___x_2609_;
}
}
v___jp_2603_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2580_, v_inst_2581_, v_inst_2582_, v_pre_2583_, v_post_2584_, v_usedLetOnly_2585_, v_skipConstInApp_2586_, v_skipInstances_2579_, v_postApp_2587_, v_x_2588_, v_x_2589_, v_f_2595_, v___y_2597_);
v___x_2605_ = lean_apply_4(v_toBind_2591_, lean_box(0), lean_box(0), v___x_2604_, v___f_2602_);
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_skipInstances_2610_ = _args[0];
lean_object* v_inst_2611_ = _args[1];
lean_object* v_inst_2612_ = _args[2];
lean_object* v_inst_2613_ = _args[3];
lean_object* v_pre_2614_ = _args[4];
lean_object* v_post_2615_ = _args[5];
lean_object* v_usedLetOnly_2616_ = _args[6];
lean_object* v_skipConstInApp_2617_ = _args[7];
lean_object* v_postApp_2618_ = _args[8];
lean_object* v_x_2619_ = _args[9];
lean_object* v_x_2620_ = _args[10];
lean_object* v___y_2621_ = _args[11];
lean_object* v_toBind_2622_ = _args[12];
lean_object* v___x_2623_ = _args[13];
lean_object* v_toApplicative_2624_ = _args[14];
lean_object* v___f_2625_ = _args[15];
lean_object* v_f_2626_ = _args[16];
lean_object* v_args_2627_ = _args[17];
lean_object* v___y_2628_ = _args[18];
_start:
{
uint8_t v_skipInstances_boxed_2629_; uint8_t v_usedLetOnly_boxed_2630_; uint8_t v_skipConstInApp_boxed_2631_; lean_object* v_res_2632_; 
v_skipInstances_boxed_2629_ = lean_unbox(v_skipInstances_2610_);
v_usedLetOnly_boxed_2630_ = lean_unbox(v_usedLetOnly_2616_);
v_skipConstInApp_boxed_2631_ = lean_unbox(v_skipConstInApp_2617_);
v_res_2632_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_skipInstances_boxed_2629_, v_inst_2611_, v_inst_2612_, v_inst_2613_, v_pre_2614_, v_post_2615_, v_usedLetOnly_boxed_2630_, v_skipConstInApp_boxed_2631_, v_postApp_2618_, v_x_2619_, v_x_2620_, v___y_2621_, v_toBind_2622_, v___x_2623_, v_toApplicative_2624_, v___f_2625_, v_f_2626_, v_args_2627_, v___y_2628_);
lean_dec(v___y_2628_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(lean_object* v_expr_2633_, lean_object* v_data_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_pre_2638_, lean_object* v_post_2639_, uint8_t v_usedLetOnly_2640_, uint8_t v_skipConstInApp_2641_, uint8_t v_skipInstances_2642_, lean_object* v_postApp_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v_a_2648_){
_start:
{
size_t v___x_2649_; size_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_ptr_addr(v_expr_2633_);
v___x_2650_ = lean_ptr_addr(v_a_2648_);
v___x_2651_ = lean_usize_dec_eq(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec_ref(v___y_2647_);
v___x_2652_ = l_Lean_Expr_mdata___override(v_data_2634_, v_a_2648_);
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2635_, v_inst_2636_, v_inst_2637_, v_pre_2638_, v_post_2639_, v_usedLetOnly_2640_, v_skipConstInApp_2641_, v_skipInstances_2642_, v_postApp_2643_, v_x_2644_, v_x_2645_, v___x_2652_, v___y_2646_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; 
lean_dec_ref(v_a_2648_);
lean_dec(v_data_2634_);
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2635_, v_inst_2636_, v_inst_2637_, v_pre_2638_, v_post_2639_, v_usedLetOnly_2640_, v_skipConstInApp_2641_, v_skipInstances_2642_, v_postApp_2643_, v_x_2644_, v_x_2645_, v___y_2647_, v___y_2646_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object* v_expr_2655_, lean_object* v_data_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_pre_2660_, lean_object* v_post_2661_, lean_object* v_usedLetOnly_2662_, lean_object* v_skipConstInApp_2663_, lean_object* v_skipInstances_2664_, lean_object* v_postApp_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v_a_2670_){
_start:
{
uint8_t v_usedLetOnly_boxed_2671_; uint8_t v_skipConstInApp_boxed_2672_; uint8_t v_skipInstances_boxed_2673_; lean_object* v_res_2674_; 
v_usedLetOnly_boxed_2671_ = lean_unbox(v_usedLetOnly_2662_);
v_skipConstInApp_boxed_2672_ = lean_unbox(v_skipConstInApp_2663_);
v_skipInstances_boxed_2673_ = lean_unbox(v_skipInstances_2664_);
v_res_2674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_expr_2655_, v_data_2656_, v_inst_2657_, v_inst_2658_, v_inst_2659_, v_pre_2660_, v_post_2661_, v_usedLetOnly_boxed_2671_, v_skipConstInApp_boxed_2672_, v_skipInstances_boxed_2673_, v_postApp_2665_, v_x_2666_, v_x_2667_, v___y_2668_, v___y_2669_, v_a_2670_);
lean_dec(v___y_2668_);
lean_dec_ref(v_expr_2655_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_struct_2675_, lean_object* v_typeName_2676_, lean_object* v_idx_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_pre_2681_, lean_object* v_post_2682_, uint8_t v_usedLetOnly_2683_, uint8_t v_skipConstInApp_2684_, uint8_t v_skipInstances_2685_, lean_object* v_postApp_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v_a_2691_){
_start:
{
size_t v___x_2692_; size_t v___x_2693_; uint8_t v___x_2694_; 
v___x_2692_ = lean_ptr_addr(v_struct_2675_);
v___x_2693_ = lean_ptr_addr(v_a_2691_);
v___x_2694_ = lean_usize_dec_eq(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec_ref(v___y_2690_);
v___x_2695_ = l_Lean_Expr_proj___override(v_typeName_2676_, v_idx_2677_, v_a_2691_);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2678_, v_inst_2679_, v_inst_2680_, v_pre_2681_, v_post_2682_, v_usedLetOnly_2683_, v_skipConstInApp_2684_, v_skipInstances_2685_, v_postApp_2686_, v_x_2687_, v_x_2688_, v___x_2695_, v___y_2689_);
return v___x_2696_;
}
else
{
lean_object* v___x_2697_; 
lean_dec_ref(v_a_2691_);
lean_dec(v_idx_2677_);
lean_dec(v_typeName_2676_);
v___x_2697_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2678_, v_inst_2679_, v_inst_2680_, v_pre_2681_, v_post_2682_, v_usedLetOnly_2683_, v_skipConstInApp_2684_, v_skipInstances_2685_, v_postApp_2686_, v_x_2687_, v_x_2688_, v___y_2690_, v___y_2689_);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_struct_2698_ = _args[0];
lean_object* v_typeName_2699_ = _args[1];
lean_object* v_idx_2700_ = _args[2];
lean_object* v_inst_2701_ = _args[3];
lean_object* v_inst_2702_ = _args[4];
lean_object* v_inst_2703_ = _args[5];
lean_object* v_pre_2704_ = _args[6];
lean_object* v_post_2705_ = _args[7];
lean_object* v_usedLetOnly_2706_ = _args[8];
lean_object* v_skipConstInApp_2707_ = _args[9];
lean_object* v_skipInstances_2708_ = _args[10];
lean_object* v_postApp_2709_ = _args[11];
lean_object* v_x_2710_ = _args[12];
lean_object* v_x_2711_ = _args[13];
lean_object* v___y_2712_ = _args[14];
lean_object* v___y_2713_ = _args[15];
lean_object* v_a_2714_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2715_; uint8_t v_skipConstInApp_boxed_2716_; uint8_t v_skipInstances_boxed_2717_; lean_object* v_res_2718_; 
v_usedLetOnly_boxed_2715_ = lean_unbox(v_usedLetOnly_2706_);
v_skipConstInApp_boxed_2716_ = lean_unbox(v_skipConstInApp_2707_);
v_skipInstances_boxed_2717_ = lean_unbox(v_skipInstances_2708_);
v_res_2718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_struct_2698_, v_typeName_2699_, v_idx_2700_, v_inst_2701_, v_inst_2702_, v_inst_2703_, v_pre_2704_, v_post_2705_, v_usedLetOnly_boxed_2715_, v_skipConstInApp_boxed_2716_, v_skipInstances_boxed_2717_, v_postApp_2709_, v_x_2710_, v_x_2711_, v___y_2712_, v___y_2713_, v_a_2714_);
lean_dec(v___y_2712_);
lean_dec_ref(v_struct_2698_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_pre_2723_, lean_object* v_post_2724_, uint8_t v_usedLetOnly_2725_, uint8_t v_skipConstInApp_2726_, uint8_t v_skipInstances_2727_, lean_object* v_postApp_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v___y_2731_, lean_object* v_toBind_2732_, lean_object* v___x_2733_, lean_object* v___f_2734_, lean_object* v_e_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___y_2738_; 
switch(lean_obj_tag(v_a_2736_))
{
case 0:
{
lean_object* v_e_2774_; lean_object* v_toPure_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v_e_2735_);
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec(v_x_2730_);
lean_dec(v_postApp_2728_);
lean_dec(v_post_2724_);
lean_dec(v_pre_2723_);
lean_dec_ref(v_inst_2722_);
lean_dec(v_inst_2721_);
lean_dec_ref(v_inst_2720_);
v_e_2774_ = lean_ctor_get(v_a_2736_, 0);
lean_inc_ref(v_e_2774_);
lean_dec_ref_known(v_a_2736_, 1);
v_toPure_2775_ = lean_ctor_get(v_toApplicative_2719_, 1);
lean_inc(v_toPure_2775_);
lean_dec_ref(v_toApplicative_2719_);
v___x_2776_ = lean_apply_2(v_toPure_2775_, lean_box(0), v_e_2774_);
return v___x_2776_;
}
case 1:
{
lean_object* v_e_2777_; lean_object* v___x_2778_; 
lean_dec_ref(v_e_2735_);
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec_ref(v_toApplicative_2719_);
v_e_2777_ = lean_ctor_get(v_a_2736_, 0);
lean_inc_ref(v_e_2777_);
lean_dec_ref_known(v_a_2736_, 1);
v___x_2778_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v_e_2777_, v___y_2731_);
return v___x_2778_;
}
default: 
{
lean_object* v_e_x3f_2779_; 
v_e_x3f_2779_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_e_x3f_2779_);
lean_dec_ref_known(v_a_2736_, 1);
if (lean_obj_tag(v_e_x3f_2779_) == 0)
{
v___y_2738_ = v_e_2735_;
goto v___jp_2737_;
}
else
{
lean_object* v_val_2780_; 
lean_dec_ref(v_e_2735_);
v_val_2780_ = lean_ctor_get(v_e_x3f_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v_e_x3f_2779_, 1);
v___y_2738_ = v_val_2780_;
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
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec_ref(v_toApplicative_2719_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v___x_2739_, v___y_2738_, v___y_2731_);
return v___x_2740_;
}
case 6:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec_ref(v_toApplicative_2719_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v___x_2741_, v___y_2738_, v___y_2731_);
return v___x_2742_;
}
case 8:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec_ref(v_toApplicative_2719_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v___x_2743_, v___y_2738_, v___y_2731_);
return v___x_2744_;
}
case 5:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v_dummy_2749_; lean_object* v_nargs_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_3395__overap_2754_; lean_object* v___x_2755_; 
v___x_2745_ = lean_box(v_skipInstances_2727_);
v___x_2746_ = lean_box(v_usedLetOnly_2725_);
v___x_2747_ = lean_box(v_skipConstInApp_2726_);
lean_inc_ref(v___y_2738_);
v___f_2748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 19, 16);
lean_closure_set(v___f_2748_, 0, v___x_2745_);
lean_closure_set(v___f_2748_, 1, v_inst_2720_);
lean_closure_set(v___f_2748_, 2, v_inst_2721_);
lean_closure_set(v___f_2748_, 3, v_inst_2722_);
lean_closure_set(v___f_2748_, 4, v_pre_2723_);
lean_closure_set(v___f_2748_, 5, v_post_2724_);
lean_closure_set(v___f_2748_, 6, v___x_2746_);
lean_closure_set(v___f_2748_, 7, v___x_2747_);
lean_closure_set(v___f_2748_, 8, v_postApp_2728_);
lean_closure_set(v___f_2748_, 9, v_x_2729_);
lean_closure_set(v___f_2748_, 10, v_x_2730_);
lean_closure_set(v___f_2748_, 11, v___y_2738_);
lean_closure_set(v___f_2748_, 12, v_toBind_2732_);
lean_closure_set(v___f_2748_, 13, v___x_2733_);
lean_closure_set(v___f_2748_, 14, v_toApplicative_2719_);
lean_closure_set(v___f_2748_, 15, v___f_2734_);
v_dummy_2749_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2750_ = l_Lean_Expr_getAppNumArgs(v___y_2738_);
lean_inc(v_nargs_2750_);
v___x_2751_ = lean_mk_array(v_nargs_2750_, v_dummy_2749_);
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_sub(v_nargs_2750_, v___x_2752_);
lean_dec(v_nargs_2750_);
v___x_3395__overap_2754_ = l_Lean_Expr_withAppAux___redArg(v___f_2748_, v___y_2738_, v___x_2751_, v___x_2753_);
lean_inc(v___y_2731_);
v___x_2755_ = lean_apply_1(v___x_3395__overap_2754_, v___y_2731_);
return v___x_2755_;
}
case 10:
{
lean_object* v_data_2756_; lean_object* v_expr_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_toApplicative_2719_);
v_data_2756_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_data_2756_);
v_expr_2757_ = lean_ctor_get(v___y_2738_, 1);
lean_inc_ref_n(v_expr_2757_, 2);
v___x_2758_ = lean_box(v_usedLetOnly_2725_);
v___x_2759_ = lean_box(v_skipConstInApp_2726_);
v___x_2760_ = lean_box(v_skipInstances_2727_);
lean_inc(v___y_2731_);
lean_inc(v_x_2730_);
lean_inc(v_postApp_2728_);
lean_inc(v_post_2724_);
lean_inc(v_pre_2723_);
lean_inc_ref(v_inst_2722_);
lean_inc(v_inst_2721_);
lean_inc_ref(v_inst_2720_);
v___f_2761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 16, 15);
lean_closure_set(v___f_2761_, 0, v_expr_2757_);
lean_closure_set(v___f_2761_, 1, v_data_2756_);
lean_closure_set(v___f_2761_, 2, v_inst_2720_);
lean_closure_set(v___f_2761_, 3, v_inst_2721_);
lean_closure_set(v___f_2761_, 4, v_inst_2722_);
lean_closure_set(v___f_2761_, 5, v_pre_2723_);
lean_closure_set(v___f_2761_, 6, v_post_2724_);
lean_closure_set(v___f_2761_, 7, v___x_2758_);
lean_closure_set(v___f_2761_, 8, v___x_2759_);
lean_closure_set(v___f_2761_, 9, v___x_2760_);
lean_closure_set(v___f_2761_, 10, v_postApp_2728_);
lean_closure_set(v___f_2761_, 11, v_x_2729_);
lean_closure_set(v___f_2761_, 12, v_x_2730_);
lean_closure_set(v___f_2761_, 13, v___y_2731_);
lean_closure_set(v___f_2761_, 14, v___y_2738_);
v___x_2762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v_expr_2757_, v___y_2731_);
v___x_2763_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2762_, v___f_2761_);
return v___x_2763_;
}
case 11:
{
lean_object* v_typeName_2764_; lean_object* v_idx_2765_; lean_object* v_struct_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_toApplicative_2719_);
v_typeName_2764_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_typeName_2764_);
v_idx_2765_ = lean_ctor_get(v___y_2738_, 1);
lean_inc(v_idx_2765_);
v_struct_2766_ = lean_ctor_get(v___y_2738_, 2);
lean_inc_ref_n(v_struct_2766_, 2);
v___x_2767_ = lean_box(v_usedLetOnly_2725_);
v___x_2768_ = lean_box(v_skipConstInApp_2726_);
v___x_2769_ = lean_box(v_skipInstances_2727_);
lean_inc(v___y_2731_);
lean_inc(v_x_2730_);
lean_inc(v_postApp_2728_);
lean_inc(v_post_2724_);
lean_inc(v_pre_2723_);
lean_inc_ref(v_inst_2722_);
lean_inc(v_inst_2721_);
lean_inc_ref(v_inst_2720_);
v___f_2770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_2770_, 0, v_struct_2766_);
lean_closure_set(v___f_2770_, 1, v_typeName_2764_);
lean_closure_set(v___f_2770_, 2, v_idx_2765_);
lean_closure_set(v___f_2770_, 3, v_inst_2720_);
lean_closure_set(v___f_2770_, 4, v_inst_2721_);
lean_closure_set(v___f_2770_, 5, v_inst_2722_);
lean_closure_set(v___f_2770_, 6, v_pre_2723_);
lean_closure_set(v___f_2770_, 7, v_post_2724_);
lean_closure_set(v___f_2770_, 8, v___x_2767_);
lean_closure_set(v___f_2770_, 9, v___x_2768_);
lean_closure_set(v___f_2770_, 10, v___x_2769_);
lean_closure_set(v___f_2770_, 11, v_postApp_2728_);
lean_closure_set(v___f_2770_, 12, v_x_2729_);
lean_closure_set(v___f_2770_, 13, v_x_2730_);
lean_closure_set(v___f_2770_, 14, v___y_2731_);
lean_closure_set(v___f_2770_, 15, v___y_2738_);
v___x_2771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v_struct_2766_, v___y_2731_);
v___x_2772_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2771_, v___f_2770_);
return v___x_2772_;
}
default: 
{
lean_object* v___x_2773_; 
lean_dec(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec(v_toBind_2732_);
lean_dec_ref(v_toApplicative_2719_);
v___x_2773_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_2725_, v_skipConstInApp_2726_, v_skipInstances_2727_, v_postApp_2728_, v_x_2729_, v_x_2730_, v___y_2738_, v___y_2731_);
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_toApplicative_2781_ = _args[0];
lean_object* v_inst_2782_ = _args[1];
lean_object* v_inst_2783_ = _args[2];
lean_object* v_inst_2784_ = _args[3];
lean_object* v_pre_2785_ = _args[4];
lean_object* v_post_2786_ = _args[5];
lean_object* v_usedLetOnly_2787_ = _args[6];
lean_object* v_skipConstInApp_2788_ = _args[7];
lean_object* v_skipInstances_2789_ = _args[8];
lean_object* v_postApp_2790_ = _args[9];
lean_object* v_x_2791_ = _args[10];
lean_object* v_x_2792_ = _args[11];
lean_object* v___y_2793_ = _args[12];
lean_object* v_toBind_2794_ = _args[13];
lean_object* v___x_2795_ = _args[14];
lean_object* v___f_2796_ = _args[15];
lean_object* v_e_2797_ = _args[16];
lean_object* v_a_2798_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2799_; uint8_t v_skipConstInApp_boxed_2800_; uint8_t v_skipInstances_boxed_2801_; lean_object* v_res_2802_; 
v_usedLetOnly_boxed_2799_ = lean_unbox(v_usedLetOnly_2787_);
v_skipConstInApp_boxed_2800_ = lean_unbox(v_skipConstInApp_2788_);
v_skipInstances_boxed_2801_ = lean_unbox(v_skipInstances_2789_);
v_res_2802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2781_, v_inst_2782_, v_inst_2783_, v_inst_2784_, v_pre_2785_, v_post_2786_, v_usedLetOnly_boxed_2799_, v_skipConstInApp_boxed_2800_, v_skipInstances_boxed_2801_, v_postApp_2790_, v_x_2791_, v_x_2792_, v___y_2793_, v_toBind_2794_, v___x_2795_, v___f_2796_, v_e_2797_, v_a_2798_);
lean_dec(v___y_2793_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v_toApplicative_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_pre_2807_, lean_object* v_post_2808_, uint8_t v_usedLetOnly_2809_, uint8_t v_skipConstInApp_2810_, uint8_t v_skipInstances_2811_, lean_object* v_postApp_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_toBind_2815_, lean_object* v___x_2816_, lean_object* v___f_2817_, lean_object* v_e_2818_, lean_object* v_____r_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___f_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2821_ = lean_box(v_usedLetOnly_2809_);
v___x_2822_ = lean_box(v_skipConstInApp_2810_);
v___x_2823_ = lean_box(v_skipInstances_2811_);
lean_inc_ref(v_e_2818_);
lean_inc(v_toBind_2815_);
lean_inc(v___y_2820_);
lean_inc(v_pre_2807_);
v___f_2824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2824_, 0, v_toApplicative_2803_);
lean_closure_set(v___f_2824_, 1, v_inst_2804_);
lean_closure_set(v___f_2824_, 2, v_inst_2805_);
lean_closure_set(v___f_2824_, 3, v_inst_2806_);
lean_closure_set(v___f_2824_, 4, v_pre_2807_);
lean_closure_set(v___f_2824_, 5, v_post_2808_);
lean_closure_set(v___f_2824_, 6, v___x_2821_);
lean_closure_set(v___f_2824_, 7, v___x_2822_);
lean_closure_set(v___f_2824_, 8, v___x_2823_);
lean_closure_set(v___f_2824_, 9, v_postApp_2812_);
lean_closure_set(v___f_2824_, 10, v_x_2813_);
lean_closure_set(v___f_2824_, 11, v_x_2814_);
lean_closure_set(v___f_2824_, 12, v___y_2820_);
lean_closure_set(v___f_2824_, 13, v_toBind_2815_);
lean_closure_set(v___f_2824_, 14, v___x_2816_);
lean_closure_set(v___f_2824_, 15, v___f_2817_);
lean_closure_set(v___f_2824_, 16, v_e_2818_);
v___x_2825_ = lean_apply_1(v_pre_2807_, v_e_2818_);
v___x_2826_ = lean_apply_4(v_toBind_2815_, lean_box(0), lean_box(0), v___x_2825_, v___f_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_toApplicative_2827_ = _args[0];
lean_object* v_inst_2828_ = _args[1];
lean_object* v_inst_2829_ = _args[2];
lean_object* v_inst_2830_ = _args[3];
lean_object* v_pre_2831_ = _args[4];
lean_object* v_post_2832_ = _args[5];
lean_object* v_usedLetOnly_2833_ = _args[6];
lean_object* v_skipConstInApp_2834_ = _args[7];
lean_object* v_skipInstances_2835_ = _args[8];
lean_object* v_postApp_2836_ = _args[9];
lean_object* v_x_2837_ = _args[10];
lean_object* v_x_2838_ = _args[11];
lean_object* v_toBind_2839_ = _args[12];
lean_object* v___x_2840_ = _args[13];
lean_object* v___f_2841_ = _args[14];
lean_object* v_e_2842_ = _args[15];
lean_object* v_____r_2843_ = _args[16];
lean_object* v___y_2844_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2845_; uint8_t v_skipConstInApp_boxed_2846_; uint8_t v_skipInstances_boxed_2847_; lean_object* v_res_2848_; 
v_usedLetOnly_boxed_2845_ = lean_unbox(v_usedLetOnly_2833_);
v_skipConstInApp_boxed_2846_ = lean_unbox(v_skipConstInApp_2834_);
v_skipInstances_boxed_2847_ = lean_unbox(v_skipInstances_2835_);
v_res_2848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v_toApplicative_2827_, v_inst_2828_, v_inst_2829_, v_inst_2830_, v_pre_2831_, v_post_2832_, v_usedLetOnly_boxed_2845_, v_skipConstInApp_boxed_2846_, v_skipInstances_boxed_2847_, v_postApp_2836_, v_x_2837_, v_x_2838_, v_toBind_2839_, v___x_2840_, v___f_2841_, v_e_2842_, v_____r_2843_, v___y_2844_);
lean_dec(v___y_2844_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_pre_2852_, lean_object* v_post_2853_, uint8_t v_usedLetOnly_2854_, uint8_t v_skipConstInApp_2855_, uint8_t v_skipInstances_2856_, lean_object* v_postApp_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_, lean_object* v_e_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___f_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; lean_object* v_toApplicative_2869_; lean_object* v_toBind_2870_; lean_object* v___f_2871_; lean_object* v___f_2872_; lean_object* v___f_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___f_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2863_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2849_, 2);
v___x_2864_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2858_, v___x_2862_, v___x_2863_, v_inst_2849_);
v___x_2865_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2858_, v___x_2862_, v___x_2863_);
lean_inc_ref_n(v_inst_2851_, 2);
lean_inc_ref(v___x_2865_);
v___f_2866_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2866_, 0, v___x_2865_);
lean_closure_set(v___f_2866_, 1, v_inst_2851_);
v___f_2867_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2867_, 0, v___x_2865_);
lean_closure_set(v___f_2867_, 1, v_inst_2851_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___f_2866_);
lean_ctor_set(v___x_2868_, 1, v___f_2867_);
v_toApplicative_2869_ = lean_ctor_get(v_inst_2849_, 0);
lean_inc_ref_n(v_toApplicative_2869_, 5);
v_toBind_2870_ = lean_ctor_get(v_inst_2849_, 1);
lean_inc_n(v_toBind_2870_, 5);
v___f_2871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2871_, 0, v_toApplicative_2869_);
lean_inc_ref_n(v_e_2860_, 2);
v___f_2872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2872_, 0, v_toApplicative_2869_);
lean_closure_set(v___f_2872_, 1, v___x_2862_);
lean_closure_set(v___f_2872_, 2, v___x_2863_);
lean_closure_set(v___f_2872_, 3, v_e_2860_);
lean_inc_n(v_x_2859_, 2);
lean_inc_n(v_a_2861_, 3);
v___f_2873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2873_, 0, v_toApplicative_2869_);
lean_closure_set(v___f_2873_, 1, v___x_2862_);
lean_closure_set(v___f_2873_, 2, v___x_2863_);
lean_closure_set(v___f_2873_, 3, v_e_2860_);
lean_closure_set(v___f_2873_, 4, v_a_2861_);
lean_closure_set(v___f_2873_, 5, v_x_2859_);
lean_closure_set(v___f_2873_, 6, v_toBind_2870_);
v___x_2874_ = lean_box(v_usedLetOnly_2854_);
v___x_2875_ = lean_box(v_skipConstInApp_2855_);
v___x_2876_ = lean_box(v_skipInstances_2856_);
lean_inc_ref(v___x_2864_);
lean_inc(v_inst_2850_);
v___f_2877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed), 18, 16);
lean_closure_set(v___f_2877_, 0, v_toApplicative_2869_);
lean_closure_set(v___f_2877_, 1, v_inst_2849_);
lean_closure_set(v___f_2877_, 2, v_inst_2850_);
lean_closure_set(v___f_2877_, 3, v_inst_2851_);
lean_closure_set(v___f_2877_, 4, v_pre_2852_);
lean_closure_set(v___f_2877_, 5, v_post_2853_);
lean_closure_set(v___f_2877_, 6, v___x_2874_);
lean_closure_set(v___f_2877_, 7, v___x_2875_);
lean_closure_set(v___f_2877_, 8, v___x_2876_);
lean_closure_set(v___f_2877_, 9, v_postApp_2857_);
lean_closure_set(v___f_2877_, 10, v_x_2858_);
lean_closure_set(v___f_2877_, 11, v_x_2859_);
lean_closure_set(v___f_2877_, 12, v_toBind_2870_);
lean_closure_set(v___f_2877_, 13, v___x_2864_);
lean_closure_set(v___f_2877_, 14, v___f_2871_);
lean_closure_set(v___f_2877_, 15, v_e_2860_);
v___f_2878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_2878_, 0, v_inst_2850_);
lean_closure_set(v___f_2878_, 1, v_x_2858_);
lean_closure_set(v___f_2878_, 2, v___x_2862_);
lean_closure_set(v___f_2878_, 3, v___x_2863_);
lean_closure_set(v___f_2878_, 4, v_inst_2849_);
lean_closure_set(v___f_2878_, 5, v___f_2877_);
lean_closure_set(v___f_2878_, 6, v___x_2868_);
lean_closure_set(v___f_2878_, 7, v___x_2864_);
lean_closure_set(v___f_2878_, 8, v_a_2861_);
lean_closure_set(v___f_2878_, 9, v_toBind_2870_);
lean_closure_set(v___f_2878_, 10, v___f_2873_);
lean_closure_set(v___f_2878_, 11, v_toApplicative_2869_);
v___x_2879_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2879_, 0, lean_box(0));
lean_closure_set(v___x_2879_, 1, lean_box(0));
lean_closure_set(v___x_2879_, 2, v_a_2861_);
v___x_2880_ = lean_apply_2(v_x_2859_, lean_box(0), v___x_2879_);
v___x_2881_ = lean_apply_4(v_toBind_2870_, lean_box(0), lean_box(0), v___x_2880_, v___f_2872_);
v___x_2882_ = lean_apply_4(v_toBind_2870_, lean_box(0), lean_box(0), v___x_2881_, v___f_2878_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_pre_2887_, lean_object* v_post_2888_, uint8_t v_usedLetOnly_2889_, uint8_t v_skipConstInApp_2890_, uint8_t v_skipInstances_2891_, lean_object* v_postApp_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_, lean_object* v_a_2895_, lean_object* v_e_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___y_2899_; 
switch(lean_obj_tag(v_a_2897_))
{
case 0:
{
lean_object* v_e_2902_; lean_object* v_toPure_2903_; lean_object* v___x_2904_; 
lean_dec_ref(v_e_2896_);
lean_dec(v_x_2894_);
lean_dec(v_postApp_2892_);
lean_dec(v_post_2888_);
lean_dec(v_pre_2887_);
lean_dec_ref(v_inst_2886_);
lean_dec(v_inst_2885_);
lean_dec_ref(v_inst_2884_);
v_e_2902_ = lean_ctor_get(v_a_2897_, 0);
lean_inc_ref(v_e_2902_);
lean_dec_ref_known(v_a_2897_, 1);
v_toPure_2903_ = lean_ctor_get(v_toApplicative_2883_, 1);
lean_inc(v_toPure_2903_);
lean_dec_ref(v_toApplicative_2883_);
v___x_2904_ = lean_apply_2(v_toPure_2903_, lean_box(0), v_e_2902_);
return v___x_2904_;
}
case 1:
{
lean_object* v_e_2905_; lean_object* v___x_2906_; 
lean_dec_ref(v_e_2896_);
lean_dec_ref(v_toApplicative_2883_);
v_e_2905_ = lean_ctor_get(v_a_2897_, 0);
lean_inc_ref(v_e_2905_);
lean_dec_ref_known(v_a_2897_, 1);
v___x_2906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2884_, v_inst_2885_, v_inst_2886_, v_pre_2887_, v_post_2888_, v_usedLetOnly_2889_, v_skipConstInApp_2890_, v_skipInstances_2891_, v_postApp_2892_, v_x_2893_, v_x_2894_, v_e_2905_, v_a_2895_);
return v___x_2906_;
}
default: 
{
lean_object* v_e_x3f_2907_; 
lean_dec(v_x_2894_);
lean_dec(v_postApp_2892_);
lean_dec(v_post_2888_);
lean_dec(v_pre_2887_);
lean_dec_ref(v_inst_2886_);
lean_dec(v_inst_2885_);
lean_dec_ref(v_inst_2884_);
v_e_x3f_2907_ = lean_ctor_get(v_a_2897_, 0);
lean_inc(v_e_x3f_2907_);
lean_dec_ref_known(v_a_2897_, 1);
if (lean_obj_tag(v_e_x3f_2907_) == 0)
{
v___y_2899_ = v_e_2896_;
goto v___jp_2898_;
}
else
{
lean_object* v_val_2908_; 
lean_dec_ref(v_e_2896_);
v_val_2908_ = lean_ctor_get(v_e_x3f_2907_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v_e_x3f_2907_, 1);
v___y_2899_ = v_val_2908_;
goto v___jp_2898_;
}
}
}
v___jp_2898_:
{
lean_object* v_toPure_2900_; lean_object* v___x_2901_; 
v_toPure_2900_ = lean_ctor_get(v_toApplicative_2883_, 1);
lean_inc(v_toPure_2900_);
lean_dec_ref(v_toApplicative_2883_);
v___x_2901_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___y_2899_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_pre_2913_, lean_object* v_post_2914_, lean_object* v_usedLetOnly_2915_, lean_object* v_skipConstInApp_2916_, lean_object* v_skipInstances_2917_, lean_object* v_postApp_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_a_2921_, lean_object* v_e_2922_, lean_object* v_a_2923_){
_start:
{
uint8_t v_usedLetOnly_boxed_2924_; uint8_t v_skipConstInApp_boxed_2925_; uint8_t v_skipInstances_boxed_2926_; lean_object* v_res_2927_; 
v_usedLetOnly_boxed_2924_ = lean_unbox(v_usedLetOnly_2915_);
v_skipConstInApp_boxed_2925_ = lean_unbox(v_skipConstInApp_2916_);
v_skipInstances_boxed_2926_ = lean_unbox(v_skipInstances_2917_);
v_res_2927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2909_, v_inst_2910_, v_inst_2911_, v_inst_2912_, v_pre_2913_, v_post_2914_, v_usedLetOnly_boxed_2924_, v_skipConstInApp_boxed_2925_, v_skipInstances_boxed_2926_, v_postApp_2918_, v_x_2919_, v_x_2920_, v_a_2921_, v_e_2922_, v_a_2923_);
lean_dec(v_a_2921_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_pre_2931_, lean_object* v_post_2932_, uint8_t v_usedLetOnly_2933_, uint8_t v_skipConstInApp_2934_, uint8_t v_skipInstances_2935_, lean_object* v_postApp_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_, lean_object* v_e_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_toApplicative_2941_; lean_object* v_toBind_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_toApplicative_2941_ = lean_ctor_get(v_inst_2928_, 0);
lean_inc_ref(v_toApplicative_2941_);
v_toBind_2942_ = lean_ctor_get(v_inst_2928_, 1);
lean_inc(v_toBind_2942_);
v___x_2943_ = lean_box(v_usedLetOnly_2933_);
v___x_2944_ = lean_box(v_skipConstInApp_2934_);
v___x_2945_ = lean_box(v_skipInstances_2935_);
lean_inc_ref(v_e_2939_);
lean_inc(v_a_2940_);
lean_inc(v_post_2932_);
v___f_2946_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 15, 14);
lean_closure_set(v___f_2946_, 0, v_toApplicative_2941_);
lean_closure_set(v___f_2946_, 1, v_inst_2928_);
lean_closure_set(v___f_2946_, 2, v_inst_2929_);
lean_closure_set(v___f_2946_, 3, v_inst_2930_);
lean_closure_set(v___f_2946_, 4, v_pre_2931_);
lean_closure_set(v___f_2946_, 5, v_post_2932_);
lean_closure_set(v___f_2946_, 6, v___x_2943_);
lean_closure_set(v___f_2946_, 7, v___x_2944_);
lean_closure_set(v___f_2946_, 8, v___x_2945_);
lean_closure_set(v___f_2946_, 9, v_postApp_2936_);
lean_closure_set(v___f_2946_, 10, v_x_2937_);
lean_closure_set(v___f_2946_, 11, v_x_2938_);
lean_closure_set(v___f_2946_, 12, v_a_2940_);
lean_closure_set(v___f_2946_, 13, v_e_2939_);
v___x_2947_ = lean_apply_1(v_post_2932_, v_e_2939_);
v___x_2948_ = lean_apply_4(v_toBind_2942_, lean_box(0), lean_box(0), v___x_2947_, v___f_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_pre_2952_, lean_object* v_post_2953_, uint8_t v_usedLetOnly_2954_, uint8_t v_skipConstInApp_2955_, uint8_t v_skipInstances_2956_, lean_object* v_postApp_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2949_, v_inst_2950_, v_inst_2951_, v_pre_2952_, v_post_2953_, v_usedLetOnly_2954_, v_skipConstInApp_2955_, v_skipInstances_2956_, v_postApp_2957_, v_x_2958_, v_x_2959_, v_a_2961_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_pre_2966_, lean_object* v_post_2967_, lean_object* v_usedLetOnly_2968_, lean_object* v_skipConstInApp_2969_, lean_object* v_skipInstances_2970_, lean_object* v_postApp_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_e_2974_, lean_object* v_a_2975_){
_start:
{
uint8_t v_usedLetOnly_boxed_2976_; uint8_t v_skipConstInApp_boxed_2977_; uint8_t v_skipInstances_boxed_2978_; lean_object* v_res_2979_; 
v_usedLetOnly_boxed_2976_ = lean_unbox(v_usedLetOnly_2968_);
v_skipConstInApp_boxed_2977_ = lean_unbox(v_skipConstInApp_2969_);
v_skipInstances_boxed_2978_ = lean_unbox(v_skipInstances_2970_);
v_res_2979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2963_, v_inst_2964_, v_inst_2965_, v_pre_2966_, v_post_2967_, v_usedLetOnly_boxed_2976_, v_skipConstInApp_boxed_2977_, v_skipInstances_boxed_2978_, v_postApp_2971_, v_x_2972_, v_x_2973_, v_e_2974_, v_a_2975_);
lean_dec(v_a_2975_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_pre_2983_, lean_object* v_post_2984_, lean_object* v_usedLetOnly_2985_, lean_object* v_skipConstInApp_2986_, lean_object* v_skipInstances_2987_, lean_object* v_postApp_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v_fvars_2991_, lean_object* v_e_2992_, lean_object* v_a_2993_){
_start:
{
uint8_t v_usedLetOnly_boxed_2994_; uint8_t v_skipConstInApp_boxed_2995_; uint8_t v_skipInstances_boxed_2996_; lean_object* v_res_2997_; 
v_usedLetOnly_boxed_2994_ = lean_unbox(v_usedLetOnly_2985_);
v_skipConstInApp_boxed_2995_ = lean_unbox(v_skipConstInApp_2986_);
v_skipInstances_boxed_2996_ = lean_unbox(v_skipInstances_2987_);
v_res_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2980_, v_inst_2981_, v_inst_2982_, v_pre_2983_, v_post_2984_, v_usedLetOnly_boxed_2994_, v_skipConstInApp_boxed_2995_, v_skipInstances_boxed_2996_, v_postApp_2988_, v_x_2989_, v_x_2990_, v_fvars_2991_, v_e_2992_, v_a_2993_);
lean_dec(v_a_2993_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_pre_3001_, lean_object* v_post_3002_, lean_object* v_usedLetOnly_3003_, lean_object* v_skipConstInApp_3004_, lean_object* v_skipInstances_3005_, lean_object* v_postApp_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_fvars_3009_, lean_object* v_e_3010_, lean_object* v_a_3011_){
_start:
{
uint8_t v_usedLetOnly_boxed_3012_; uint8_t v_skipConstInApp_boxed_3013_; uint8_t v_skipInstances_boxed_3014_; lean_object* v_res_3015_; 
v_usedLetOnly_boxed_3012_ = lean_unbox(v_usedLetOnly_3003_);
v_skipConstInApp_boxed_3013_ = lean_unbox(v_skipConstInApp_3004_);
v_skipInstances_boxed_3014_ = lean_unbox(v_skipInstances_3005_);
v_res_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2998_, v_inst_2999_, v_inst_3000_, v_pre_3001_, v_post_3002_, v_usedLetOnly_boxed_3012_, v_skipConstInApp_boxed_3013_, v_skipInstances_boxed_3014_, v_postApp_3006_, v_x_3007_, v_x_3008_, v_fvars_3009_, v_e_3010_, v_a_3011_);
lean_dec(v_a_3011_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_pre_3019_, lean_object* v_post_3020_, lean_object* v_usedLetOnly_3021_, lean_object* v_skipConstInApp_3022_, lean_object* v_skipInstances_3023_, lean_object* v_postApp_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_fvars_3027_, lean_object* v_e_3028_, lean_object* v_a_3029_){
_start:
{
uint8_t v_usedLetOnly_boxed_3030_; uint8_t v_skipConstInApp_boxed_3031_; uint8_t v_skipInstances_boxed_3032_; lean_object* v_res_3033_; 
v_usedLetOnly_boxed_3030_ = lean_unbox(v_usedLetOnly_3021_);
v_skipConstInApp_boxed_3031_ = lean_unbox(v_skipConstInApp_3022_);
v_skipInstances_boxed_3032_ = lean_unbox(v_skipInstances_3023_);
v_res_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3016_, v_inst_3017_, v_inst_3018_, v_pre_3019_, v_post_3020_, v_usedLetOnly_boxed_3030_, v_skipConstInApp_boxed_3031_, v_skipInstances_boxed_3032_, v_postApp_3024_, v_x_3025_, v_x_3026_, v_fvars_3027_, v_e_3028_, v_a_3029_);
lean_dec(v_a_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_pre_3038_, lean_object* v_post_3039_, uint8_t v_usedLetOnly_3040_, uint8_t v_skipConstInApp_3041_, uint8_t v_skipInstances_3042_, lean_object* v_postApp_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_e_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3035_, v_inst_3036_, v_inst_3037_, v_pre_3038_, v_post_3039_, v_usedLetOnly_3040_, v_skipConstInApp_3041_, v_skipInstances_3042_, v_postApp_3043_, v_x_3044_, v_x_3045_, v_e_3046_, v_a_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_pre_3053_, lean_object* v_post_3054_, lean_object* v_usedLetOnly_3055_, lean_object* v_skipConstInApp_3056_, lean_object* v_skipInstances_3057_, lean_object* v_postApp_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_, lean_object* v_e_3061_, lean_object* v_a_3062_){
_start:
{
uint8_t v_usedLetOnly_boxed_3063_; uint8_t v_skipConstInApp_boxed_3064_; uint8_t v_skipInstances_boxed_3065_; lean_object* v_res_3066_; 
v_usedLetOnly_boxed_3063_ = lean_unbox(v_usedLetOnly_3055_);
v_skipConstInApp_boxed_3064_ = lean_unbox(v_skipConstInApp_3056_);
v_skipInstances_boxed_3065_ = lean_unbox(v_skipInstances_3057_);
v_res_3066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_pre_3053_, v_post_3054_, v_usedLetOnly_boxed_3063_, v_skipConstInApp_boxed_3064_, v_skipInstances_boxed_3065_, v_postApp_3058_, v_x_3059_, v_x_3060_, v_e_3061_, v_a_3062_);
lean_dec(v_a_3062_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_pre_3071_, lean_object* v_post_3072_, uint8_t v_usedLetOnly_3073_, uint8_t v_skipConstInApp_3074_, uint8_t v_skipInstances_3075_, lean_object* v_postApp_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_fvars_3079_, lean_object* v_e_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3068_, v_inst_3069_, v_inst_3070_, v_pre_3071_, v_post_3072_, v_usedLetOnly_3073_, v_skipConstInApp_3074_, v_skipInstances_3075_, v_postApp_3076_, v_x_3077_, v_x_3078_, v_fvars_3079_, v_e_3080_, v_a_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_pre_3087_, lean_object* v_post_3088_, lean_object* v_usedLetOnly_3089_, lean_object* v_skipConstInApp_3090_, lean_object* v_skipInstances_3091_, lean_object* v_postApp_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v_fvars_3095_, lean_object* v_e_3096_, lean_object* v_a_3097_){
_start:
{
uint8_t v_usedLetOnly_boxed_3098_; uint8_t v_skipConstInApp_boxed_3099_; uint8_t v_skipInstances_boxed_3100_; lean_object* v_res_3101_; 
v_usedLetOnly_boxed_3098_ = lean_unbox(v_usedLetOnly_3089_);
v_skipConstInApp_boxed_3099_ = lean_unbox(v_skipConstInApp_3090_);
v_skipInstances_boxed_3100_ = lean_unbox(v_skipInstances_3091_);
v_res_3101_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3083_, v_inst_3084_, v_inst_3085_, v_inst_3086_, v_pre_3087_, v_post_3088_, v_usedLetOnly_boxed_3098_, v_skipConstInApp_boxed_3099_, v_skipInstances_boxed_3100_, v_postApp_3092_, v_x_3093_, v_x_3094_, v_fvars_3095_, v_e_3096_, v_a_3097_);
lean_dec(v_a_3097_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_pre_3106_, lean_object* v_post_3107_, uint8_t v_usedLetOnly_3108_, uint8_t v_skipConstInApp_3109_, uint8_t v_skipInstances_3110_, lean_object* v_postApp_3111_, lean_object* v_x_3112_, lean_object* v_x_3113_, lean_object* v_e_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3103_, v_inst_3104_, v_inst_3105_, v_pre_3106_, v_post_3107_, v_usedLetOnly_3108_, v_skipConstInApp_3109_, v_skipInstances_3110_, v_postApp_3111_, v_x_3112_, v_x_3113_, v_e_3114_, v_a_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_pre_3121_, lean_object* v_post_3122_, lean_object* v_usedLetOnly_3123_, lean_object* v_skipConstInApp_3124_, lean_object* v_skipInstances_3125_, lean_object* v_postApp_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v_e_3129_, lean_object* v_a_3130_){
_start:
{
uint8_t v_usedLetOnly_boxed_3131_; uint8_t v_skipConstInApp_boxed_3132_; uint8_t v_skipInstances_boxed_3133_; lean_object* v_res_3134_; 
v_usedLetOnly_boxed_3131_ = lean_unbox(v_usedLetOnly_3123_);
v_skipConstInApp_boxed_3132_ = lean_unbox(v_skipConstInApp_3124_);
v_skipInstances_boxed_3133_ = lean_unbox(v_skipInstances_3125_);
v_res_3134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3117_, v_inst_3118_, v_inst_3119_, v_inst_3120_, v_pre_3121_, v_post_3122_, v_usedLetOnly_boxed_3131_, v_skipConstInApp_boxed_3132_, v_skipInstances_boxed_3133_, v_postApp_3126_, v_x_3127_, v_x_3128_, v_e_3129_, v_a_3130_);
lean_dec(v_a_3130_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_pre_3139_, lean_object* v_post_3140_, uint8_t v_usedLetOnly_3141_, uint8_t v_skipConstInApp_3142_, uint8_t v_skipInstances_3143_, lean_object* v_postApp_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_, lean_object* v_fvars_3147_, lean_object* v_e_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3136_, v_inst_3137_, v_inst_3138_, v_pre_3139_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v_postApp_3144_, v_x_3145_, v_x_3146_, v_fvars_3147_, v_e_3148_, v_a_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_pre_3155_, lean_object* v_post_3156_, lean_object* v_usedLetOnly_3157_, lean_object* v_skipConstInApp_3158_, lean_object* v_skipInstances_3159_, lean_object* v_postApp_3160_, lean_object* v_x_3161_, lean_object* v_x_3162_, lean_object* v_fvars_3163_, lean_object* v_e_3164_, lean_object* v_a_3165_){
_start:
{
uint8_t v_usedLetOnly_boxed_3166_; uint8_t v_skipConstInApp_boxed_3167_; uint8_t v_skipInstances_boxed_3168_; lean_object* v_res_3169_; 
v_usedLetOnly_boxed_3166_ = lean_unbox(v_usedLetOnly_3157_);
v_skipConstInApp_boxed_3167_ = lean_unbox(v_skipConstInApp_3158_);
v_skipInstances_boxed_3168_ = lean_unbox(v_skipInstances_3159_);
v_res_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3151_, v_inst_3152_, v_inst_3153_, v_inst_3154_, v_pre_3155_, v_post_3156_, v_usedLetOnly_boxed_3166_, v_skipConstInApp_boxed_3167_, v_skipInstances_boxed_3168_, v_postApp_3160_, v_x_3161_, v_x_3162_, v_fvars_3163_, v_e_3164_, v_a_3165_);
lean_dec(v_a_3165_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_pre_3174_, lean_object* v_post_3175_, uint8_t v_usedLetOnly_3176_, uint8_t v_skipConstInApp_3177_, uint8_t v_skipInstances_3178_, lean_object* v_postApp_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_, lean_object* v_fvars_3182_, lean_object* v_e_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3171_, v_inst_3172_, v_inst_3173_, v_pre_3174_, v_post_3175_, v_usedLetOnly_3176_, v_skipConstInApp_3177_, v_skipInstances_3178_, v_postApp_3179_, v_x_3180_, v_x_3181_, v_fvars_3182_, v_e_3183_, v_a_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_pre_3190_, lean_object* v_post_3191_, lean_object* v_usedLetOnly_3192_, lean_object* v_skipConstInApp_3193_, lean_object* v_skipInstances_3194_, lean_object* v_postApp_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_, lean_object* v_fvars_3198_, lean_object* v_e_3199_, lean_object* v_a_3200_){
_start:
{
uint8_t v_usedLetOnly_boxed_3201_; uint8_t v_skipConstInApp_boxed_3202_; uint8_t v_skipInstances_boxed_3203_; lean_object* v_res_3204_; 
v_usedLetOnly_boxed_3201_ = lean_unbox(v_usedLetOnly_3192_);
v_skipConstInApp_boxed_3202_ = lean_unbox(v_skipConstInApp_3193_);
v_skipInstances_boxed_3203_ = lean_unbox(v_skipInstances_3194_);
v_res_3204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3186_, v_inst_3187_, v_inst_3188_, v_inst_3189_, v_pre_3190_, v_post_3191_, v_usedLetOnly_boxed_3201_, v_skipConstInApp_boxed_3202_, v_skipInstances_boxed_3203_, v_postApp_3195_, v_x_3196_, v_x_3197_, v_fvars_3198_, v_e_3199_, v_a_3200_);
lean_dec(v_a_3200_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_apply_1(v_x_3205_, lean_box(0));
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3220_, lean_object* v_00_u03b1_3221_, lean_object* v_x_3222_){
_start:
{
lean_object* v___f_3223_; lean_object* v___x_3224_; 
v___f_3223_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3223_, 0, v_x_3222_);
v___x_3224_ = lean_apply_2(v_inst_3220_, lean_box(0), v___f_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3225_, lean_object* v_x_3226_, lean_object* v_toBind_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_pre_3231_, lean_object* v_post_3232_, uint8_t v_usedLetOnly_3233_, uint8_t v_skipConstInApp_3234_, uint8_t v_skipInstances_3235_, lean_object* v_postApp_3236_, lean_object* v_x_3237_, lean_object* v_input_3238_, lean_object* v_ref_3239_){
_start:
{
lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_inc(v_toBind_3227_);
lean_inc(v_x_3226_);
lean_inc(v_ref_3239_);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3240_, 0, v_toPure_3225_);
lean_closure_set(v___f_3240_, 1, v_ref_3239_);
lean_closure_set(v___f_3240_, 2, v_x_3226_);
lean_closure_set(v___f_3240_, 3, v_toBind_3227_);
v___x_3241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3228_, v_inst_3229_, v_inst_3230_, v_pre_3231_, v_post_3232_, v_usedLetOnly_3233_, v_skipConstInApp_3234_, v_skipInstances_3235_, v_postApp_3236_, v_x_3237_, v_x_3226_, v_input_3238_, v_ref_3239_);
lean_dec(v_ref_3239_);
v___x_3242_ = lean_apply_4(v_toBind_3227_, lean_box(0), lean_box(0), v___x_3241_, v___f_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3243_, lean_object* v_x_3244_, lean_object* v_toBind_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_pre_3249_, lean_object* v_post_3250_, lean_object* v_usedLetOnly_3251_, lean_object* v_skipConstInApp_3252_, lean_object* v_skipInstances_3253_, lean_object* v_postApp_3254_, lean_object* v_x_3255_, lean_object* v_input_3256_, lean_object* v_ref_3257_){
_start:
{
uint8_t v_usedLetOnly_boxed_3258_; uint8_t v_skipConstInApp_boxed_3259_; uint8_t v_skipInstances_boxed_3260_; lean_object* v_res_3261_; 
v_usedLetOnly_boxed_3258_ = lean_unbox(v_usedLetOnly_3251_);
v_skipConstInApp_boxed_3259_ = lean_unbox(v_skipConstInApp_3252_);
v_skipInstances_boxed_3260_ = lean_unbox(v_skipInstances_3253_);
v_res_3261_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3243_, v_x_3244_, v_toBind_3245_, v_inst_3246_, v_inst_3247_, v_inst_3248_, v_pre_3249_, v_post_3250_, v_usedLetOnly_boxed_3258_, v_skipConstInApp_boxed_3259_, v_skipInstances_boxed_3260_, v_postApp_3254_, v_x_3255_, v_input_3256_, v_ref_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_input_3265_, lean_object* v_cache_3266_, lean_object* v_pre_3267_, lean_object* v_post_3268_, uint8_t v_usedLetOnly_3269_, uint8_t v_skipConstInApp_3270_, uint8_t v_skipInstances_3271_, lean_object* v_postApp_3272_){
_start:
{
lean_object* v_x_3273_; lean_object* v_toApplicative_3274_; lean_object* v_toBind_3275_; lean_object* v_toPure_3276_; lean_object* v_x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; 
v_x_3273_ = lean_box(0);
v_toApplicative_3274_ = lean_ctor_get(v_inst_3262_, 0);
v_toBind_3275_ = lean_ctor_get(v_inst_3262_, 1);
lean_inc_n(v_toBind_3275_, 2);
v_toPure_3276_ = lean_ctor_get(v_toApplicative_3274_, 1);
lean_inc(v_toPure_3276_);
lean_inc_n(v_inst_3263_, 2);
v_x_3277_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3277_, 0, v_inst_3263_);
v___x_3278_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3278_, 0, lean_box(0));
lean_closure_set(v___x_3278_, 1, lean_box(0));
lean_closure_set(v___x_3278_, 2, v_cache_3266_);
v___x_3279_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3263_, lean_box(0), v___x_3278_);
v___x_3280_ = lean_box(v_usedLetOnly_3269_);
v___x_3281_ = lean_box(v_skipConstInApp_3270_);
v___x_3282_ = lean_box(v_skipInstances_3271_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3283_, 0, v_toPure_3276_);
lean_closure_set(v___f_3283_, 1, v_x_3277_);
lean_closure_set(v___f_3283_, 2, v_toBind_3275_);
lean_closure_set(v___f_3283_, 3, v_inst_3262_);
lean_closure_set(v___f_3283_, 4, v_inst_3263_);
lean_closure_set(v___f_3283_, 5, v_inst_3264_);
lean_closure_set(v___f_3283_, 6, v_pre_3267_);
lean_closure_set(v___f_3283_, 7, v_post_3268_);
lean_closure_set(v___f_3283_, 8, v___x_3280_);
lean_closure_set(v___f_3283_, 9, v___x_3281_);
lean_closure_set(v___f_3283_, 10, v___x_3282_);
lean_closure_set(v___f_3283_, 11, v_postApp_3272_);
lean_closure_set(v___f_3283_, 12, v_x_3273_);
lean_closure_set(v___f_3283_, 13, v_input_3265_);
v___x_3284_ = lean_apply_4(v_toBind_3275_, lean_box(0), lean_box(0), v___x_3279_, v___f_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_input_3288_, lean_object* v_cache_3289_, lean_object* v_pre_3290_, lean_object* v_post_3291_, lean_object* v_usedLetOnly_3292_, lean_object* v_skipConstInApp_3293_, lean_object* v_skipInstances_3294_, lean_object* v_postApp_3295_){
_start:
{
uint8_t v_usedLetOnly_boxed_3296_; uint8_t v_skipConstInApp_boxed_3297_; uint8_t v_skipInstances_boxed_3298_; lean_object* v_res_3299_; 
v_usedLetOnly_boxed_3296_ = lean_unbox(v_usedLetOnly_3292_);
v_skipConstInApp_boxed_3297_ = lean_unbox(v_skipConstInApp_3293_);
v_skipInstances_boxed_3298_ = lean_unbox(v_skipInstances_3294_);
v_res_3299_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3285_, v_inst_3286_, v_inst_3287_, v_input_3288_, v_cache_3289_, v_pre_3290_, v_post_3291_, v_usedLetOnly_boxed_3296_, v_skipConstInApp_boxed_3297_, v_skipInstances_boxed_3298_, v_postApp_3295_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_input_3304_, lean_object* v_cache_3305_, lean_object* v_pre_3306_, lean_object* v_post_3307_, uint8_t v_usedLetOnly_3308_, uint8_t v_skipConstInApp_3309_, uint8_t v_skipInstances_3310_, lean_object* v_postApp_3311_){
_start:
{
lean_object* v_x_3312_; lean_object* v_toApplicative_3313_; lean_object* v_toBind_3314_; lean_object* v_toPure_3315_; lean_object* v_x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___f_3322_; lean_object* v___x_3323_; 
v_x_3312_ = lean_box(0);
v_toApplicative_3313_ = lean_ctor_get(v_inst_3301_, 0);
v_toBind_3314_ = lean_ctor_get(v_inst_3301_, 1);
lean_inc_n(v_toBind_3314_, 2);
v_toPure_3315_ = lean_ctor_get(v_toApplicative_3313_, 1);
lean_inc(v_toPure_3315_);
lean_inc_n(v_inst_3302_, 2);
v_x_3316_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3316_, 0, v_inst_3302_);
v___x_3317_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3317_, 0, lean_box(0));
lean_closure_set(v___x_3317_, 1, lean_box(0));
lean_closure_set(v___x_3317_, 2, v_cache_3305_);
v___x_3318_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3302_, lean_box(0), v___x_3317_);
v___x_3319_ = lean_box(v_usedLetOnly_3308_);
v___x_3320_ = lean_box(v_skipConstInApp_3309_);
v___x_3321_ = lean_box(v_skipInstances_3310_);
v___f_3322_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3322_, 0, v_toPure_3315_);
lean_closure_set(v___f_3322_, 1, v_x_3316_);
lean_closure_set(v___f_3322_, 2, v_toBind_3314_);
lean_closure_set(v___f_3322_, 3, v_inst_3301_);
lean_closure_set(v___f_3322_, 4, v_inst_3302_);
lean_closure_set(v___f_3322_, 5, v_inst_3303_);
lean_closure_set(v___f_3322_, 6, v_pre_3306_);
lean_closure_set(v___f_3322_, 7, v_post_3307_);
lean_closure_set(v___f_3322_, 8, v___x_3319_);
lean_closure_set(v___f_3322_, 9, v___x_3320_);
lean_closure_set(v___f_3322_, 10, v___x_3321_);
lean_closure_set(v___f_3322_, 11, v_postApp_3311_);
lean_closure_set(v___f_3322_, 12, v_x_3312_);
lean_closure_set(v___f_3322_, 13, v_input_3304_);
v___x_3323_ = lean_apply_4(v_toBind_3314_, lean_box(0), lean_box(0), v___x_3318_, v___f_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3324_, lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_input_3328_, lean_object* v_cache_3329_, lean_object* v_pre_3330_, lean_object* v_post_3331_, lean_object* v_usedLetOnly_3332_, lean_object* v_skipConstInApp_3333_, lean_object* v_skipInstances_3334_, lean_object* v_postApp_3335_){
_start:
{
uint8_t v_usedLetOnly_boxed_3336_; uint8_t v_skipConstInApp_boxed_3337_; uint8_t v_skipInstances_boxed_3338_; lean_object* v_res_3339_; 
v_usedLetOnly_boxed_3336_ = lean_unbox(v_usedLetOnly_3332_);
v_skipConstInApp_boxed_3337_ = lean_unbox(v_skipConstInApp_3333_);
v_skipInstances_boxed_3338_ = lean_unbox(v_skipInstances_3334_);
v_res_3339_ = l_Lean_Meta_transformWithCache(v_m_3324_, v_inst_3325_, v_inst_3326_, v_inst_3327_, v_input_3328_, v_cache_3329_, v_pre_3330_, v_post_3331_, v_usedLetOnly_boxed_3336_, v_skipConstInApp_boxed_3337_, v_skipInstances_boxed_3338_, v_postApp_3335_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2(lean_object* v_toPure_3340_, lean_object* v_x_3341_, lean_object* v_e_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_apply_2(v_toPure_3340_, lean_box(0), v_e_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__2___boxed(lean_object* v_toPure_3344_, lean_object* v_x_3345_, lean_object* v_e_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Meta_transform___redArg___lam__2(v_toPure_3344_, v_x_3345_, v_e_3346_);
lean_dec_ref(v_x_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4(lean_object* v_toPure_3348_, lean_object* v_x_3349_, lean_object* v_toBind_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_pre_3354_, lean_object* v_post_3355_, uint8_t v_usedLetOnly_3356_, uint8_t v_skipConstInApp_3357_, uint8_t v___x_3358_, lean_object* v___f_3359_, lean_object* v_x_3360_, lean_object* v_input_3361_, lean_object* v_ref_3362_){
_start:
{
lean_object* v___f_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_inc(v_toBind_3350_);
lean_inc(v_x_3349_);
lean_inc(v_ref_3362_);
v___f_3363_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3363_, 0, v_toPure_3348_);
lean_closure_set(v___f_3363_, 1, v_ref_3362_);
lean_closure_set(v___f_3363_, 2, v_x_3349_);
lean_closure_set(v___f_3363_, 3, v_toBind_3350_);
v___x_3364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3351_, v_inst_3352_, v_inst_3353_, v_pre_3354_, v_post_3355_, v_usedLetOnly_3356_, v_skipConstInApp_3357_, v___x_3358_, v___f_3359_, v_x_3360_, v_x_3349_, v_input_3361_, v_ref_3362_);
lean_dec(v_ref_3362_);
v___x_3365_ = lean_apply_4(v_toBind_3350_, lean_box(0), lean_box(0), v___x_3364_, v___f_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__4___boxed(lean_object* v_toPure_3366_, lean_object* v_x_3367_, lean_object* v_toBind_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_pre_3372_, lean_object* v_post_3373_, lean_object* v_usedLetOnly_3374_, lean_object* v_skipConstInApp_3375_, lean_object* v___x_3376_, lean_object* v___f_3377_, lean_object* v_x_3378_, lean_object* v_input_3379_, lean_object* v_ref_3380_){
_start:
{
uint8_t v_usedLetOnly_boxed_3381_; uint8_t v_skipConstInApp_boxed_3382_; uint8_t v___x_129__boxed_3383_; lean_object* v_res_3384_; 
v_usedLetOnly_boxed_3381_ = lean_unbox(v_usedLetOnly_3374_);
v_skipConstInApp_boxed_3382_ = lean_unbox(v_skipConstInApp_3375_);
v___x_129__boxed_3383_ = lean_unbox(v___x_3376_);
v_res_3384_ = l_Lean_Meta_transform___redArg___lam__4(v_toPure_3366_, v_x_3367_, v_toBind_3368_, v_inst_3369_, v_inst_3370_, v_inst_3371_, v_pre_3372_, v_post_3373_, v_usedLetOnly_boxed_3381_, v_skipConstInApp_boxed_3382_, v___x_129__boxed_3383_, v___f_3377_, v_x_3378_, v_input_3379_, v_ref_3380_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_input_3388_, lean_object* v_pre_3389_, lean_object* v_post_3390_, uint8_t v_usedLetOnly_3391_, uint8_t v_skipConstInApp_3392_){
_start:
{
lean_object* v_toApplicative_3393_; lean_object* v_toBind_3394_; lean_object* v_toPure_3395_; lean_object* v_x_3396_; uint8_t v___x_3397_; lean_object* v___f_3398_; lean_object* v___f_3399_; lean_object* v_x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_toApplicative_3393_ = lean_ctor_get(v_inst_3385_, 0);
v_toBind_3394_ = lean_ctor_get(v_inst_3385_, 1);
lean_inc_n(v_toBind_3394_, 3);
v_toPure_3395_ = lean_ctor_get(v_toApplicative_3393_, 1);
lean_inc_n(v_toPure_3395_, 3);
lean_inc_n(v_inst_3386_, 2);
v_x_3396_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3396_, 0, v_inst_3386_);
v___x_3397_ = 0;
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3398_, 0, v_toPure_3395_);
v___f_3399_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3399_, 0, v_toPure_3395_);
v_x_3400_ = lean_box(0);
v___x_3401_ = lean_box(v_usedLetOnly_3391_);
v___x_3402_ = lean_box(v_skipConstInApp_3392_);
v___x_3403_ = lean_box(v___x_3397_);
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_3404_, 0, v_toPure_3395_);
lean_closure_set(v___f_3404_, 1, v_x_3396_);
lean_closure_set(v___f_3404_, 2, v_toBind_3394_);
lean_closure_set(v___f_3404_, 3, v_inst_3385_);
lean_closure_set(v___f_3404_, 4, v_inst_3386_);
lean_closure_set(v___f_3404_, 5, v_inst_3387_);
lean_closure_set(v___f_3404_, 6, v_pre_3389_);
lean_closure_set(v___f_3404_, 7, v_post_3390_);
lean_closure_set(v___f_3404_, 8, v___x_3401_);
lean_closure_set(v___f_3404_, 9, v___x_3402_);
lean_closure_set(v___f_3404_, 10, v___x_3403_);
lean_closure_set(v___f_3404_, 11, v___f_3398_);
lean_closure_set(v___f_3404_, 12, v_x_3400_);
lean_closure_set(v___f_3404_, 13, v_input_3388_);
v___x_3405_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3406_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3386_, lean_box(0), v___x_3405_);
v___x_3407_ = lean_apply_4(v_toBind_3394_, lean_box(0), lean_box(0), v___x_3406_, v___f_3404_);
v___x_3408_ = lean_apply_4(v_toBind_3394_, lean_box(0), lean_box(0), v___x_3407_, v___f_3399_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3409_, lean_object* v_inst_3410_, lean_object* v_inst_3411_, lean_object* v_input_3412_, lean_object* v_pre_3413_, lean_object* v_post_3414_, lean_object* v_usedLetOnly_3415_, lean_object* v_skipConstInApp_3416_){
_start:
{
uint8_t v_usedLetOnly_boxed_3417_; uint8_t v_skipConstInApp_boxed_3418_; lean_object* v_res_3419_; 
v_usedLetOnly_boxed_3417_ = lean_unbox(v_usedLetOnly_3415_);
v_skipConstInApp_boxed_3418_ = lean_unbox(v_skipConstInApp_3416_);
v_res_3419_ = l_Lean_Meta_transform___redArg(v_inst_3409_, v_inst_3410_, v_inst_3411_, v_input_3412_, v_pre_3413_, v_post_3414_, v_usedLetOnly_boxed_3417_, v_skipConstInApp_boxed_3418_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_input_3424_, lean_object* v_pre_3425_, lean_object* v_post_3426_, uint8_t v_usedLetOnly_3427_, uint8_t v_skipConstInApp_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_Meta_transform___redArg(v_inst_3421_, v_inst_3422_, v_inst_3423_, v_input_3424_, v_pre_3425_, v_post_3426_, v_usedLetOnly_3427_, v_skipConstInApp_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3430_, lean_object* v_inst_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_input_3434_, lean_object* v_pre_3435_, lean_object* v_post_3436_, lean_object* v_usedLetOnly_3437_, lean_object* v_skipConstInApp_3438_){
_start:
{
uint8_t v_usedLetOnly_boxed_3439_; uint8_t v_skipConstInApp_boxed_3440_; lean_object* v_res_3441_; 
v_usedLetOnly_boxed_3439_ = lean_unbox(v_usedLetOnly_3437_);
v_skipConstInApp_boxed_3440_ = lean_unbox(v_skipConstInApp_3438_);
v_res_3441_ = l_Lean_Meta_transform(v_m_3430_, v_inst_3431_, v_inst_3432_, v_inst_3433_, v_input_3434_, v_pre_3435_, v_post_3436_, v_usedLetOnly_boxed_3439_, v_skipConstInApp_boxed_3440_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = l_Lean_Expr_hasMVar(v_e_3442_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_e_3442_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; lean_object* v_mctx_3448_; lean_object* v___x_3449_; lean_object* v_fst_3450_; lean_object* v_snd_3451_; lean_object* v___x_3452_; lean_object* v_cache_3453_; lean_object* v_zetaDeltaFVarIds_3454_; lean_object* v_postponed_3455_; lean_object* v_diag_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3465_; 
v___x_3447_ = lean_st_ref_get(v___y_3443_);
v_mctx_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc_ref(v_mctx_3448_);
lean_dec(v___x_3447_);
v___x_3449_ = l_Lean_instantiateMVarsCore(v_mctx_3448_, v_e_3442_);
v_fst_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_fst_3450_);
v_snd_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_snd_3451_);
lean_dec_ref(v___x_3449_);
v___x_3452_ = lean_st_ref_take(v___y_3443_);
v_cache_3453_ = lean_ctor_get(v___x_3452_, 1);
v_zetaDeltaFVarIds_3454_ = lean_ctor_get(v___x_3452_, 2);
v_postponed_3455_ = lean_ctor_get(v___x_3452_, 3);
v_diag_3456_ = lean_ctor_get(v___x_3452_, 4);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3466_);
v___x_3458_ = v___x_3452_;
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_diag_3456_);
lean_inc(v_postponed_3455_);
lean_inc(v_zetaDeltaFVarIds_3454_);
lean_inc(v_cache_3453_);
lean_dec(v___x_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v_snd_3451_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_snd_3451_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_cache_3453_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_zetaDeltaFVarIds_3454_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_postponed_3455_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_diag_3456_);
v___x_3461_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_st_ref_put(v___y_3443_, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_fst_3450_);
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3467_, v___y_3468_);
lean_dec(v___y_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3471_, v___y_3473_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3485_, lean_object* v___x_3486_, uint8_t v_zetaDelta_3487_, lean_object* v_fvarId_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3488_, v___y_3489_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3523_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3523_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3523_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
if (lean_obj_tag(v_a_3495_) == 1)
{
lean_object* v_val_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3518_; 
v_val_3499_ = lean_ctor_get(v_a_3495_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3501_ = v_a_3495_;
v_isShared_3502_ = v_isSharedCheck_3518_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_val_3499_);
lean_dec(v_a_3495_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3518_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
uint8_t v___y_3504_; 
if (v_zetaDelta_3487_ == 0)
{
lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3512_ = l_Lean_LocalDecl_index(v_val_3499_);
v___x_3513_ = lean_nat_dec_lt(v___x_3512_, v___x_3486_);
lean_dec(v___x_3512_);
if (v___x_3513_ == 0)
{
lean_del_object(v___x_3501_);
goto v___jp_3509_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
lean_dec(v_val_3499_);
lean_del_object(v___x_3497_);
v___x_3514_ = lean_box(0);
if (v_isShared_3502_ == 0)
{
lean_ctor_set_tag(v___x_3501_, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3514_);
v___x_3516_ = v___x_3501_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_del_object(v___x_3501_);
goto v___jp_3509_;
}
v___jp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = l_Lean_LocalDecl_value_x3f(v_val_3499_, v___y_3504_);
lean_dec(v_val_3499_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3505_);
v___x_3507_ = v___x_3497_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
v___jp_3509_:
{
if (v_zetaHave_3485_ == 0)
{
v___y_3504_ = v_zetaHave_3485_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3510_ = l_Lean_LocalDecl_index(v_val_3499_);
v___x_3511_ = lean_nat_dec_le(v___x_3486_, v___x_3510_);
lean_dec(v___x_3510_);
v___y_3504_ = v___x_3511_;
goto v___jp_3503_;
}
}
}
}
else
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
lean_dec(v_a_3495_);
v___x_3519_ = lean_box(0);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3519_);
v___x_3521_ = v___x_3497_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
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
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
v_a_3524_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3494_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3494_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3532_, lean_object* v___x_3533_, lean_object* v_zetaDelta_3534_, lean_object* v_fvarId_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
uint8_t v_zetaHave_boxed_3541_; uint8_t v_zetaDelta_boxed_3542_; lean_object* v_res_3543_; 
v_zetaHave_boxed_3541_ = lean_unbox(v_zetaHave_3532_);
v_zetaDelta_boxed_3542_ = lean_unbox(v_zetaDelta_3534_);
v_res_3543_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3541_, v___x_3533_, v_zetaDelta_boxed_3542_, v_fvarId_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___x_3533_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_e_3544_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3559_, lean_object* v_e_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
if (lean_obj_tag(v_e_3560_) == 1)
{
lean_object* v_fvarId_3566_; lean_object* v___x_3567_; 
v_fvarId_3566_ = lean_ctor_get(v_e_3560_, 0);
lean_inc(v___y_3564_);
lean_inc_ref(v___y_3563_);
lean_inc(v___y_3562_);
lean_inc_ref(v___y_3561_);
lean_inc(v_fvarId_3566_);
v___x_3567_ = lean_apply_6(v___f_3559_, v_fvarId_3566_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, lean_box(0));
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3593_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3593_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3593_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_val_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3588_; 
lean_del_object(v___x_3570_);
lean_dec_ref_known(v_e_3560_, 1);
v_val_3572_ = lean_ctor_get(v_a_3568_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3574_ = v_a_3568_;
v_isShared_3575_ = v_isSharedCheck_3588_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_val_3572_);
lean_dec(v_a_3568_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3588_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3587_; 
v___x_3576_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3572_, v___y_3562_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3587_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3587_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_a_3577_);
v___x_3582_ = v___x_3574_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3582_);
v___x_3584_ = v___x_3579_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
lean_dec(v_a_3568_);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v_e_3560_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3589_);
v___x_3591_ = v___x_3570_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref_known(v_e_3560_, 1);
v_a_3594_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3567_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3567_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v_e_3560_);
lean_dec_ref(v___f_3559_);
v___x_3602_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3604_, lean_object* v_e_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3604_, v_e_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3612_, lean_object* v_e_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_Expr_getAppFn(v_e_3613_);
if (lean_obj_tag(v___x_3619_) == 1)
{
lean_object* v_fvarId_3620_; lean_object* v___x_3621_; 
v_fvarId_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_fvarId_3620_);
lean_dec_ref_known(v___x_3619_, 1);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3615_);
lean_inc_ref(v___y_3614_);
v___x_3621_ = lean_apply_6(v___f_3612_, v_fvarId_3620_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, lean_box(0));
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3654_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3654_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3654_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
if (lean_obj_tag(v_a_3622_) == 1)
{
lean_object* v_val_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3649_; 
lean_del_object(v___x_3624_);
v_val_3626_ = lean_ctor_get(v_a_3622_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3628_ = v_a_3622_;
v_isShared_3629_ = v_isSharedCheck_3649_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_val_3626_);
lean_dec(v_a_3622_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3649_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3648_; 
v___x_3630_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3626_, v___y_3615_);
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3648_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3648_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_dummy_3635_; lean_object* v_nargs_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v_dummy_3635_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3636_ = l_Lean_Expr_getAppNumArgs(v_e_3613_);
lean_inc(v_nargs_3636_);
v___x_3637_ = lean_mk_array(v_nargs_3636_, v_dummy_3635_);
v___x_3638_ = lean_unsigned_to_nat(1u);
v___x_3639_ = lean_nat_sub(v_nargs_3636_, v___x_3638_);
lean_dec(v_nargs_3636_);
v___x_3640_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3613_, v___x_3637_, v___x_3639_);
v___x_3641_ = l_Lean_Expr_beta(v_a_3631_, v___x_3640_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3641_);
v___x_3643_ = v___x_3628_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3645_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3643_);
v___x_3645_ = v___x_3633_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_dec(v_a_3622_);
lean_dec_ref(v_e_3613_);
v___x_3650_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3650_);
v___x_3652_ = v___x_3624_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
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
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec_ref(v_e_3613_);
v_a_3655_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3621_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3621_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec_ref(v___x_3619_);
lean_dec_ref(v_e_3613_);
lean_dec_ref(v___f_3612_);
v___x_3663_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3665_, lean_object* v_e_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3665_, v_e_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3673_, lean_object* v_x_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_apply_1(v_x_3674_, lean_box(0));
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_x_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3682_, v_x_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3690_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3704_, lean_object* v___y_3705_, lean_object* v_b_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v___x_3712_; 
lean_inc(v___y_3710_);
lean_inc_ref(v___y_3709_);
lean_inc(v___y_3708_);
lean_inc_ref(v___y_3707_);
lean_inc(v___y_3705_);
v___x_3712_ = lean_apply_7(v_k_3704_, v_b_3706_, v___y_3705_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, lean_box(0));
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3713_, lean_object* v___y_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3713_, v___y_3714_, v_b_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3714_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3722_, uint8_t v_bi_3723_, lean_object* v_type_3724_, lean_object* v_k_3725_, uint8_t v_kind_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___f_3733_; lean_object* v___x_3734_; 
lean_inc(v___y_3727_);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3733_, 0, v_k_3725_);
lean_closure_set(v___f_3733_, 1, v___y_3727_);
v___x_3734_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3722_, v_bi_3723_, v_type_3724_, v___f_3733_, v_kind_3726_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3734_) == 0)
{
return v___x_3734_;
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3743_, lean_object* v_bi_3744_, lean_object* v_type_3745_, lean_object* v_k_3746_, lean_object* v_kind_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
uint8_t v_bi_boxed_3754_; uint8_t v_kind_boxed_3755_; lean_object* v_res_3756_; 
v_bi_boxed_3754_ = lean_unbox(v_bi_3744_);
v_kind_boxed_3755_ = lean_unbox(v_kind_3747_);
v_res_3756_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3743_, v_bi_boxed_3754_, v_type_3745_, v_k_3746_, v_kind_boxed_3755_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3757_, lean_object* v_type_3758_, lean_object* v_val_3759_, lean_object* v_k_3760_, uint8_t v_nondep_3761_, uint8_t v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___f_3769_; lean_object* v___x_3770_; 
lean_inc(v___y_3763_);
v___f_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3769_, 0, v_k_3760_);
lean_closure_set(v___f_3769_, 1, v___y_3763_);
v___x_3770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3757_, v_type_3758_, v_val_3759_, v___f_3769_, v_nondep_3761_, v_kind_3762_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3770_) == 0)
{
return v___x_3770_;
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3779_, lean_object* v_type_3780_, lean_object* v_val_3781_, lean_object* v_k_3782_, lean_object* v_nondep_3783_, lean_object* v_kind_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_nondep_boxed_3791_; uint8_t v_kind_boxed_3792_; lean_object* v_res_3793_; 
v_nondep_boxed_3791_ = lean_unbox(v_nondep_3783_);
v_kind_boxed_3792_ = lean_unbox(v_kind_3784_);
v_res_3793_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3779_, v_type_3780_, v_val_3781_, v_k_3782_, v_nondep_boxed_3791_, v_kind_boxed_3792_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3794_, lean_object* v_x_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_apply_1(v_x_3795_, lean_box(0));
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3803_, v_x_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v_ref_3811_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3816_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___y_3827_; lean_object* v_toCold_3836_; lean_object* v_currRecDepth_3837_; lean_object* v_ref_3838_; uint16_t v_optionFlags_3839_; uint8_t v_suppressElabErrors_3840_; uint8_t v_isRecordingDeps_3841_; lean_object* v_maxRecDepth_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_toCold_3836_ = lean_ctor_get(v___y_3823_, 0);
v_currRecDepth_3837_ = lean_ctor_get(v___y_3823_, 1);
v_ref_3838_ = lean_ctor_get(v___y_3823_, 2);
v_optionFlags_3839_ = lean_ctor_get_uint16(v___y_3823_, sizeof(void*)*3);
v_suppressElabErrors_3840_ = lean_ctor_get_uint8(v___y_3823_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3841_ = lean_ctor_get_uint8(v___y_3823_, sizeof(void*)*3 + 3);
v_maxRecDepth_3847_ = lean_ctor_get(v_toCold_3836_, 3);
v___x_3848_ = lean_unsigned_to_nat(0u);
v___x_3849_ = lean_nat_dec_eq(v_maxRecDepth_3847_, v___x_3848_);
if (v___x_3849_ == 0)
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_nat_dec_eq(v_currRecDepth_3837_, v_maxRecDepth_3847_);
if (v___x_3850_ == 0)
{
goto v___jp_3842_;
}
else
{
lean_object* v___x_3851_; 
lean_dec_ref(v_x_3819_);
lean_inc(v_ref_3838_);
v___x_3851_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3838_);
v___y_3827_ = v___x_3851_;
goto v___jp_3826_;
}
}
else
{
goto v___jp_3842_;
}
v___jp_3826_:
{
if (lean_obj_tag(v___y_3827_) == 0)
{
return v___y_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v_a_3828_ = lean_ctor_get(v___y_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___y_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___y_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___y_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
v___jp_3842_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3843_ = lean_unsigned_to_nat(1u);
v___x_3844_ = lean_nat_add(v_currRecDepth_3837_, v___x_3843_);
lean_inc(v_ref_3838_);
lean_inc_ref(v_toCold_3836_);
v___x_3845_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3845_, 0, v_toCold_3836_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
lean_ctor_set(v___x_3845_, 2, v_ref_3838_);
lean_ctor_set_uint16(v___x_3845_, sizeof(void*)*3, v_optionFlags_3839_);
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*3 + 2, v_suppressElabErrors_3840_);
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*3 + 3, v_isRecordingDeps_3841_);
lean_inc(v___y_3824_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
v___x_3846_ = lean_apply_6(v_x_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___x_3845_, v___y_3824_, lean_box(0));
v___y_3827_ = v___x_3846_;
goto v___jp_3826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3860_, lean_object* v_pre_3861_, lean_object* v_post_3862_, lean_object* v_usedLetOnly_3863_, lean_object* v_skipConstInApp_3864_, lean_object* v_skipInstances_3865_, lean_object* v_postApp_3866_, lean_object* v_body_3867_, lean_object* v_x_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v_usedLetOnly_boxed_3875_; uint8_t v_skipConstInApp_boxed_3876_; uint8_t v_skipInstances_boxed_3877_; lean_object* v_res_3878_; 
v_usedLetOnly_boxed_3875_ = lean_unbox(v_usedLetOnly_3863_);
v_skipConstInApp_boxed_3876_ = lean_unbox(v_skipConstInApp_3864_);
v_skipInstances_boxed_3877_ = lean_unbox(v_skipInstances_3865_);
v_res_3878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3860_, v_pre_3861_, v_post_3862_, v_usedLetOnly_boxed_3875_, v_skipConstInApp_boxed_3876_, v_skipInstances_boxed_3877_, v_postApp_3866_, v_body_3867_, v_x_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3879_, lean_object* v_pre_3880_, lean_object* v_post_3881_, uint8_t v_usedLetOnly_3882_, uint8_t v_skipConstInApp_3883_, uint8_t v_skipInstances_3884_, lean_object* v_postApp_3885_, lean_object* v_body_3886_, lean_object* v_x_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_array_push(v_fvars_3879_, v_x_3887_);
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3880_, v_post_3881_, v_usedLetOnly_3882_, v_skipConstInApp_3883_, v_skipInstances_3884_, v_postApp_3885_, v___x_3894_, v_body_3886_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3896_, lean_object* v_pre_3897_, lean_object* v_post_3898_, lean_object* v_usedLetOnly_3899_, lean_object* v_skipConstInApp_3900_, lean_object* v_skipInstances_3901_, lean_object* v_postApp_3902_, lean_object* v_body_3903_, lean_object* v_x_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v_usedLetOnly_boxed_3911_; uint8_t v_skipConstInApp_boxed_3912_; uint8_t v_skipInstances_boxed_3913_; lean_object* v_res_3914_; 
v_usedLetOnly_boxed_3911_ = lean_unbox(v_usedLetOnly_3899_);
v_skipConstInApp_boxed_3912_ = lean_unbox(v_skipConstInApp_3900_);
v_skipInstances_boxed_3913_ = lean_unbox(v_skipInstances_3901_);
v_res_3914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3896_, v_pre_3897_, v_post_3898_, v_usedLetOnly_boxed_3911_, v_skipConstInApp_boxed_3912_, v_skipInstances_boxed_3913_, v_postApp_3902_, v_body_3903_, v_x_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3915_, lean_object* v_post_3916_, uint8_t v_usedLetOnly_3917_, uint8_t v_skipConstInApp_3918_, uint8_t v_skipInstances_3919_, lean_object* v_postApp_3920_, lean_object* v_e_3921_, lean_object* v_a_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; 
lean_inc_ref(v_post_3916_);
lean_inc(v___y_3926_);
lean_inc_ref(v___y_3925_);
lean_inc(v___y_3924_);
lean_inc_ref(v___y_3923_);
lean_inc_ref(v_e_3921_);
v___x_3928_ = lean_apply_6(v_post_3916_, v_e_3921_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, lean_box(0));
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3947_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3947_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3947_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
switch(lean_obj_tag(v_a_3929_))
{
case 0:
{
lean_object* v_e_3933_; lean_object* v___x_3935_; 
lean_dec_ref(v_e_3921_);
lean_dec_ref(v_postApp_3920_);
lean_dec_ref(v_post_3916_);
lean_dec_ref(v_pre_3915_);
v_e_3933_ = lean_ctor_get(v_a_3929_, 0);
lean_inc_ref(v_e_3933_);
lean_dec_ref_known(v_a_3929_, 1);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_e_3933_);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_e_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
case 1:
{
lean_object* v_e_3937_; lean_object* v___x_3938_; 
lean_del_object(v___x_3931_);
lean_dec_ref(v_e_3921_);
v_e_3937_ = lean_ctor_get(v_a_3929_, 0);
lean_inc_ref(v_e_3937_);
lean_dec_ref_known(v_a_3929_, 1);
v___x_3938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3915_, v_post_3916_, v_usedLetOnly_3917_, v_skipConstInApp_3918_, v_skipInstances_3919_, v_postApp_3920_, v_e_3937_, v_a_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
return v___x_3938_;
}
default: 
{
lean_object* v_e_x3f_3939_; 
lean_dec_ref(v_postApp_3920_);
lean_dec_ref(v_post_3916_);
lean_dec_ref(v_pre_3915_);
v_e_x3f_3939_ = lean_ctor_get(v_a_3929_, 0);
lean_inc(v_e_x3f_3939_);
lean_dec_ref_known(v_a_3929_, 1);
if (lean_obj_tag(v_e_x3f_3939_) == 0)
{
lean_object* v___x_3941_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_e_3921_);
v___x_3941_ = v___x_3931_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_e_3921_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
else
{
lean_object* v_val_3943_; lean_object* v___x_3945_; 
lean_dec_ref(v_e_3921_);
v_val_3943_ = lean_ctor_get(v_e_x3f_3939_, 0);
lean_inc(v_val_3943_);
lean_dec_ref_known(v_e_x3f_3939_, 1);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_val_3943_);
v___x_3945_ = v___x_3931_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_val_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v_e_3921_);
lean_dec_ref(v_postApp_3920_);
lean_dec_ref(v_post_3916_);
lean_dec_ref(v_pre_3915_);
v_a_3948_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3928_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3928_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3956_, lean_object* v_post_3957_, uint8_t v_usedLetOnly_3958_, uint8_t v_skipConstInApp_3959_, uint8_t v_skipInstances_3960_, lean_object* v_postApp_3961_, lean_object* v_fvars_3962_, lean_object* v_e_3963_, lean_object* v_a_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
if (lean_obj_tag(v_e_3963_) == 6)
{
lean_object* v_binderName_3970_; lean_object* v_binderType_3971_; lean_object* v_body_3972_; uint8_t v_binderInfo_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___f_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_binderName_3970_ = lean_ctor_get(v_e_3963_, 0);
lean_inc(v_binderName_3970_);
v_binderType_3971_ = lean_ctor_get(v_e_3963_, 1);
lean_inc_ref(v_binderType_3971_);
v_body_3972_ = lean_ctor_get(v_e_3963_, 2);
lean_inc_ref(v_body_3972_);
v_binderInfo_3973_ = lean_ctor_get_uint8(v_e_3963_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3963_, 3);
v___x_3974_ = lean_box(v_usedLetOnly_3958_);
v___x_3975_ = lean_box(v_skipConstInApp_3959_);
v___x_3976_ = lean_box(v_skipInstances_3960_);
lean_inc_ref(v_postApp_3961_);
lean_inc_ref(v_post_3957_);
lean_inc_ref(v_pre_3956_);
lean_inc_ref(v_fvars_3962_);
v___f_3977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3977_, 0, v_fvars_3962_);
lean_closure_set(v___f_3977_, 1, v_pre_3956_);
lean_closure_set(v___f_3977_, 2, v_post_3957_);
lean_closure_set(v___f_3977_, 3, v___x_3974_);
lean_closure_set(v___f_3977_, 4, v___x_3975_);
lean_closure_set(v___f_3977_, 5, v___x_3976_);
lean_closure_set(v___f_3977_, 6, v_postApp_3961_);
lean_closure_set(v___f_3977_, 7, v_body_3972_);
v___x_3978_ = lean_expr_instantiate_rev(v_binderType_3971_, v_fvars_3962_);
lean_dec_ref(v_fvars_3962_);
lean_dec_ref(v_binderType_3971_);
v___x_3979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3956_, v_post_3957_, v_usedLetOnly_3958_, v_skipConstInApp_3959_, v_skipInstances_3960_, v_postApp_3961_, v___x_3978_, v_a_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = 0;
v___x_3982_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3970_, v_binderInfo_3973_, v_a_3980_, v___f_3977_, v___x_3981_, v_a_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3982_;
}
else
{
lean_dec_ref(v___f_3977_);
lean_dec(v_binderName_3970_);
return v___x_3979_;
}
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_expr_instantiate_rev(v_e_3963_, v_fvars_3962_);
lean_dec_ref(v_e_3963_);
lean_inc_ref(v_postApp_3961_);
lean_inc_ref(v_post_3957_);
lean_inc_ref(v_pre_3956_);
v___x_3984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3956_, v_post_3957_, v_usedLetOnly_3958_, v_skipConstInApp_3959_, v_skipInstances_3960_, v_postApp_3961_, v___x_3983_, v_a_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; uint8_t v___x_3986_; uint8_t v___x_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = 0;
v___x_3987_ = 1;
v___x_3988_ = 1;
v___x_3989_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3962_, v_a_3985_, v___x_3986_, v_usedLetOnly_3958_, v___x_3986_, v___x_3987_, v___x_3988_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec_ref(v_fvars_3962_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3956_, v_post_3957_, v_usedLetOnly_3958_, v_skipConstInApp_3959_, v_skipInstances_3960_, v_postApp_3961_, v_a_3990_, v_a_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3991_;
}
else
{
lean_dec_ref(v_postApp_3961_);
lean_dec_ref(v_post_3957_);
lean_dec_ref(v_pre_3956_);
return v___x_3989_;
}
}
else
{
lean_dec_ref(v_fvars_3962_);
lean_dec_ref(v_postApp_3961_);
lean_dec_ref(v_post_3957_);
lean_dec_ref(v_pre_3956_);
return v___x_3984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3992_, lean_object* v_pre_3993_, lean_object* v_post_3994_, uint8_t v_usedLetOnly_3995_, uint8_t v_skipConstInApp_3996_, uint8_t v_skipInstances_3997_, lean_object* v_postApp_3998_, lean_object* v_body_3999_, lean_object* v_x_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_array_push(v_fvars_3992_, v_x_4000_);
v___x_4008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3993_, v_post_3994_, v_usedLetOnly_3995_, v_skipConstInApp_3996_, v_skipInstances_3997_, v_postApp_3998_, v___x_4007_, v_body_3999_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_4009_, lean_object* v_pre_4010_, lean_object* v_post_4011_, lean_object* v_usedLetOnly_4012_, lean_object* v_skipConstInApp_4013_, lean_object* v_skipInstances_4014_, lean_object* v_postApp_4015_, lean_object* v_body_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
uint8_t v_usedLetOnly_boxed_4024_; uint8_t v_skipConstInApp_boxed_4025_; uint8_t v_skipInstances_boxed_4026_; lean_object* v_res_4027_; 
v_usedLetOnly_boxed_4024_ = lean_unbox(v_usedLetOnly_4012_);
v_skipConstInApp_boxed_4025_ = lean_unbox(v_skipConstInApp_4013_);
v_skipInstances_boxed_4026_ = lean_unbox(v_skipInstances_4014_);
v_res_4027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_4009_, v_pre_4010_, v_post_4011_, v_usedLetOnly_boxed_4024_, v_skipConstInApp_boxed_4025_, v_skipInstances_boxed_4026_, v_postApp_4015_, v_body_4016_, v_x_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_4028_, lean_object* v_post_4029_, uint8_t v_usedLetOnly_4030_, uint8_t v_skipConstInApp_4031_, uint8_t v_skipInstances_4032_, lean_object* v_postApp_4033_, lean_object* v_fvars_4034_, lean_object* v_e_4035_, lean_object* v_a_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
if (lean_obj_tag(v_e_4035_) == 8)
{
lean_object* v_declName_4042_; lean_object* v_type_4043_; lean_object* v_value_4044_; lean_object* v_body_4045_; uint8_t v_nondep_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_declName_4042_ = lean_ctor_get(v_e_4035_, 0);
lean_inc(v_declName_4042_);
v_type_4043_ = lean_ctor_get(v_e_4035_, 1);
lean_inc_ref(v_type_4043_);
v_value_4044_ = lean_ctor_get(v_e_4035_, 2);
lean_inc_ref(v_value_4044_);
v_body_4045_ = lean_ctor_get(v_e_4035_, 3);
lean_inc_ref(v_body_4045_);
v_nondep_4046_ = lean_ctor_get_uint8(v_e_4035_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4035_, 4);
v___x_4047_ = lean_box(v_usedLetOnly_4030_);
v___x_4048_ = lean_box(v_skipConstInApp_4031_);
v___x_4049_ = lean_box(v_skipInstances_4032_);
lean_inc_ref_n(v_postApp_4033_, 2);
lean_inc_ref_n(v_post_4029_, 2);
lean_inc_ref_n(v_pre_4028_, 2);
lean_inc_ref(v_fvars_4034_);
v___f_4050_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4050_, 0, v_fvars_4034_);
lean_closure_set(v___f_4050_, 1, v_pre_4028_);
lean_closure_set(v___f_4050_, 2, v_post_4029_);
lean_closure_set(v___f_4050_, 3, v___x_4047_);
lean_closure_set(v___f_4050_, 4, v___x_4048_);
lean_closure_set(v___f_4050_, 5, v___x_4049_);
lean_closure_set(v___f_4050_, 6, v_postApp_4033_);
lean_closure_set(v___f_4050_, 7, v_body_4045_);
v___x_4051_ = lean_expr_instantiate_rev(v_type_4043_, v_fvars_4034_);
lean_dec_ref(v_type_4043_);
v___x_4052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4028_, v_post_4029_, v_usedLetOnly_4030_, v_skipConstInApp_4031_, v_skipInstances_4032_, v_postApp_4033_, v___x_4051_, v_a_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4052_, 1);
v___x_4054_ = lean_expr_instantiate_rev(v_value_4044_, v_fvars_4034_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_value_4044_);
v___x_4055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4028_, v_post_4029_, v_usedLetOnly_4030_, v_skipConstInApp_4031_, v_skipInstances_4032_, v_postApp_4033_, v___x_4054_, v_a_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = 0;
v___x_4058_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_4042_, v_a_4053_, v_a_4056_, v___f_4050_, v_nondep_4046_, v___x_4057_, v_a_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4058_;
}
else
{
lean_dec(v_a_4053_);
lean_dec_ref(v___f_4050_);
lean_dec(v_declName_4042_);
return v___x_4055_;
}
}
else
{
lean_dec_ref(v___f_4050_);
lean_dec_ref(v_value_4044_);
lean_dec(v_declName_4042_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_postApp_4033_);
lean_dec_ref(v_post_4029_);
lean_dec_ref(v_pre_4028_);
return v___x_4052_;
}
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_expr_instantiate_rev(v_e_4035_, v_fvars_4034_);
lean_dec_ref(v_e_4035_);
lean_inc_ref(v_postApp_4033_);
lean_inc_ref(v_post_4029_);
lean_inc_ref(v_pre_4028_);
v___x_4060_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4028_, v_post_4029_, v_usedLetOnly_4030_, v_skipConstInApp_4031_, v_skipInstances_4032_, v_postApp_4033_, v___x_4059_, v_a_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; uint8_t v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = 0;
v___x_4063_ = 1;
v___x_4064_ = l_Lean_Meta_mkLetFVars(v_fvars_4034_, v_a_4061_, v_usedLetOnly_4030_, v___x_4062_, v___x_4063_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec_ref(v_fvars_4034_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4066_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4028_, v_post_4029_, v_usedLetOnly_4030_, v_skipConstInApp_4031_, v_skipInstances_4032_, v_postApp_4033_, v_a_4065_, v_a_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4066_;
}
else
{
lean_dec_ref(v_postApp_4033_);
lean_dec_ref(v_post_4029_);
lean_dec_ref(v_pre_4028_);
return v___x_4064_;
}
}
else
{
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_postApp_4033_);
lean_dec_ref(v_post_4029_);
lean_dec_ref(v_pre_4028_);
return v___x_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_4067_, lean_object* v_post_4068_, uint8_t v_usedLetOnly_4069_, uint8_t v_skipConstInApp_4070_, uint8_t v_skipInstances_4071_, lean_object* v_postApp_4072_, size_t v_sz_4073_, size_t v_i_4074_, lean_object* v_bs_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v___x_4082_; 
v___x_4082_ = lean_usize_dec_lt(v_i_4074_, v_sz_4073_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; 
lean_dec_ref(v_postApp_4072_);
lean_dec_ref(v_post_4068_);
lean_dec_ref(v_pre_4067_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_bs_4075_);
return v___x_4083_;
}
else
{
lean_object* v_v_4084_; lean_object* v___x_4085_; lean_object* v_bs_x27_4086_; lean_object* v___x_4087_; 
v_v_4084_ = lean_array_uget(v_bs_4075_, v_i_4074_);
v___x_4085_ = lean_unsigned_to_nat(0u);
v_bs_x27_4086_ = lean_array_uset(v_bs_4075_, v_i_4074_, v___x_4085_);
lean_inc_ref(v_postApp_4072_);
lean_inc_ref(v_post_4068_);
lean_inc_ref(v_pre_4067_);
v___x_4087_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4067_, v_post_4068_, v_usedLetOnly_4069_, v_skipConstInApp_4070_, v_skipInstances_4071_, v_postApp_4072_, v_v_4084_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; size_t v___x_4089_; size_t v___x_4090_; lean_object* v___x_4091_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
v___x_4089_ = ((size_t)1ULL);
v___x_4090_ = lean_usize_add(v_i_4074_, v___x_4089_);
v___x_4091_ = lean_array_uset(v_bs_x27_4086_, v_i_4074_, v_a_4088_);
v_i_4074_ = v___x_4090_;
v_bs_4075_ = v___x_4091_;
goto _start;
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec_ref(v_bs_x27_4086_);
lean_dec_ref(v_postApp_4072_);
lean_dec_ref(v_post_4068_);
lean_dec_ref(v_pre_4067_);
v_a_4093_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4087_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4087_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4101_, lean_object* v_post_4102_, uint8_t v_usedLetOnly_4103_, uint8_t v_skipConstInApp_4104_, uint8_t v_skipInstances_4105_, lean_object* v_postApp_4106_, lean_object* v___x_4107_, lean_object* v___y_4108_, lean_object* v_b_4109_, lean_object* v_a_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4101_, v_post_4102_, v_usedLetOnly_4103_, v_skipConstInApp_4104_, v_skipInstances_4105_, v_postApp_4106_, v___x_4107_, v___y_4108_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v___x_4121_ = lean_array_fset(v_b_4109_, v_a_4110_, v_a_4117_);
v___x_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v___x_4122_);
v___x_4124_ = v___x_4119_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v_b_4109_);
v_a_4127_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4116_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4116_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4135_, lean_object* v_post_4136_, lean_object* v_usedLetOnly_4137_, lean_object* v_skipConstInApp_4138_, lean_object* v_skipInstances_4139_, lean_object* v_postApp_4140_, lean_object* v___x_4141_, lean_object* v___y_4142_, lean_object* v_b_4143_, lean_object* v_a_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
uint8_t v_usedLetOnly_boxed_4150_; uint8_t v_skipConstInApp_boxed_4151_; uint8_t v_skipInstances_boxed_4152_; lean_object* v_res_4153_; 
v_usedLetOnly_boxed_4150_ = lean_unbox(v_usedLetOnly_4137_);
v_skipConstInApp_boxed_4151_ = lean_unbox(v_skipConstInApp_4138_);
v_skipInstances_boxed_4152_ = lean_unbox(v_skipInstances_4139_);
v_res_4153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4135_, v_post_4136_, v_usedLetOnly_boxed_4150_, v_skipConstInApp_boxed_4151_, v_skipInstances_boxed_4152_, v_postApp_4140_, v___x_4141_, v___y_4142_, v_b_4143_, v_a_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v_a_4144_);
lean_dec(v___y_4142_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4154_, lean_object* v___x_4155_, lean_object* v_pre_4156_, lean_object* v_post_4157_, uint8_t v_usedLetOnly_4158_, uint8_t v_skipConstInApp_4159_, uint8_t v_skipInstances_4160_, lean_object* v_postApp_4161_, lean_object* v_a_4162_, lean_object* v_b_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___y_4171_; uint8_t v___x_4194_; 
v___x_4194_ = lean_nat_dec_lt(v_a_4162_, v_upperBound_4154_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; 
lean_dec(v_a_4162_);
lean_dec_ref(v_postApp_4161_);
lean_dec_ref(v_post_4157_);
lean_dec_ref(v_pre_4156_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v_b_4163_);
return v___x_4195_;
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4196_ = lean_array_fget_borrowed(v_b_4163_, v_a_4162_);
v___x_4197_ = lean_array_get_size(v___x_4155_);
v___x_4198_ = lean_nat_dec_lt(v_a_4162_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___f_4202_; 
lean_inc(v___x_4196_);
v___x_4199_ = lean_box(v_usedLetOnly_4158_);
v___x_4200_ = lean_box(v_skipConstInApp_4159_);
v___x_4201_ = lean_box(v_skipInstances_4160_);
lean_inc(v_a_4162_);
lean_inc(v___y_4164_);
lean_inc_ref(v_postApp_4161_);
lean_inc_ref(v_post_4157_);
lean_inc_ref(v_pre_4156_);
v___f_4202_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_4202_, 0, v_pre_4156_);
lean_closure_set(v___f_4202_, 1, v_post_4157_);
lean_closure_set(v___f_4202_, 2, v___x_4199_);
lean_closure_set(v___f_4202_, 3, v___x_4200_);
lean_closure_set(v___f_4202_, 4, v___x_4201_);
lean_closure_set(v___f_4202_, 5, v_postApp_4161_);
lean_closure_set(v___f_4202_, 6, v___x_4196_);
lean_closure_set(v___f_4202_, 7, v___y_4164_);
lean_closure_set(v___f_4202_, 8, v_b_4163_);
lean_closure_set(v___f_4202_, 9, v_a_4162_);
v___y_4171_ = v___f_4202_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4203_; uint8_t v_isInstance_4204_; 
v___x_4203_ = lean_array_fget_borrowed(v___x_4155_, v_a_4162_);
v_isInstance_4204_ = lean_ctor_get_uint8(v___x_4203_, sizeof(void*)*1 + 4);
if (v_isInstance_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___f_4208_; 
lean_inc(v___x_4196_);
v___x_4205_ = lean_box(v_usedLetOnly_4158_);
v___x_4206_ = lean_box(v_skipConstInApp_4159_);
v___x_4207_ = lean_box(v_skipInstances_4160_);
lean_inc(v_a_4162_);
lean_inc(v___y_4164_);
lean_inc_ref(v_postApp_4161_);
lean_inc_ref(v_post_4157_);
lean_inc_ref(v_pre_4156_);
v___f_4208_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_4208_, 0, v_pre_4156_);
lean_closure_set(v___f_4208_, 1, v_post_4157_);
lean_closure_set(v___f_4208_, 2, v___x_4205_);
lean_closure_set(v___f_4208_, 3, v___x_4206_);
lean_closure_set(v___f_4208_, 4, v___x_4207_);
lean_closure_set(v___f_4208_, 5, v_postApp_4161_);
lean_closure_set(v___f_4208_, 6, v___x_4196_);
lean_closure_set(v___f_4208_, 7, v___y_4164_);
lean_closure_set(v___f_4208_, 8, v_b_4163_);
lean_closure_set(v___f_4208_, 9, v_a_4162_);
v___y_4171_ = v___f_4208_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4209_; lean_object* v___f_4210_; 
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_b_4163_);
v___f_4210_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4210_, 0, v___x_4209_);
v___y_4171_ = v___f_4210_;
goto v___jp_4170_;
}
}
}
v___jp_4170_:
{
lean_object* v___x_4172_; 
lean_inc(v___y_4168_);
lean_inc_ref(v___y_4167_);
lean_inc(v___y_4166_);
lean_inc_ref(v___y_4165_);
v___x_4172_ = lean_apply_5(v___y_4171_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, lean_box(0));
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4185_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4185_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4185_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
if (lean_obj_tag(v_a_4173_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; 
lean_dec(v_a_4162_);
lean_dec_ref(v_postApp_4161_);
lean_dec_ref(v_post_4157_);
lean_dec_ref(v_pre_4156_);
v_a_4177_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v_a_4173_, 1);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v_a_4177_);
v___x_4179_ = v___x_4175_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_del_object(v___x_4175_);
v_a_4181_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v_a_4173_, 1);
v___x_4182_ = lean_unsigned_to_nat(1u);
v___x_4183_ = lean_nat_add(v_a_4162_, v___x_4182_);
lean_dec(v_a_4162_);
v_a_4162_ = v___x_4183_;
v_b_4163_ = v_a_4181_;
goto _start;
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v_a_4162_);
lean_dec_ref(v_postApp_4161_);
lean_dec_ref(v_post_4157_);
lean_dec_ref(v_pre_4156_);
v_a_4186_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4172_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4172_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4211_, lean_object* v_pre_4212_, lean_object* v_post_4213_, uint8_t v_usedLetOnly_4214_, uint8_t v_skipConstInApp_4215_, lean_object* v_postApp_4216_, lean_object* v___y_4217_, lean_object* v_x_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_f_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; 
if (lean_obj_tag(v_x_4218_) == 5)
{
lean_object* v_fn_4280_; lean_object* v_arg_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v_fn_4280_ = lean_ctor_get(v_x_4218_, 0);
lean_inc_ref(v_fn_4280_);
v_arg_4281_ = lean_ctor_get(v_x_4218_, 1);
lean_inc_ref(v_arg_4281_);
lean_dec_ref_known(v_x_4218_, 2);
v___x_4282_ = lean_array_set(v_x_4219_, v_x_4220_, v_arg_4281_);
v___x_4283_ = lean_unsigned_to_nat(1u);
v___x_4284_ = lean_nat_sub(v_x_4220_, v___x_4283_);
lean_dec(v_x_4220_);
v_x_4218_ = v_fn_4280_;
v_x_4219_ = v___x_4282_;
v_x_4220_ = v___x_4284_;
goto _start;
}
else
{
lean_dec(v_x_4220_);
if (v_skipConstInApp_4215_ == 0)
{
goto v___jp_4277_;
}
else
{
uint8_t v___x_4286_; 
v___x_4286_ = l_Lean_Expr_isConst(v_x_4218_);
if (v___x_4286_ == 0)
{
goto v___jp_4277_;
}
else
{
v_f_4228_ = v_x_4218_;
v___y_4229_ = v___y_4221_;
v___y_4230_ = v___y_4222_;
v___y_4231_ = v___y_4223_;
v___y_4232_ = v___y_4224_;
v___y_4233_ = v___y_4225_;
goto v___jp_4227_;
}
}
}
v___jp_4227_:
{
if (v_skipInstances_4211_ == 0)
{
size_t v_sz_4234_; size_t v___x_4235_; lean_object* v___x_4236_; 
v_sz_4234_ = lean_array_size(v_x_4219_);
v___x_4235_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_4216_);
lean_inc_ref(v_post_4213_);
lean_inc_ref(v_pre_4212_);
v___x_4236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4212_, v_post_4213_, v_usedLetOnly_4214_, v_skipConstInApp_4215_, v_skipInstances_4211_, v_postApp_4216_, v_sz_4234_, v___x_4235_, v_x_4219_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = l_Lean_mkAppN(v_f_4228_, v_a_4237_);
lean_dec(v_a_4237_);
lean_inc_ref(v_postApp_4216_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc_ref(v___y_4230_);
v___x_4239_ = lean_apply_7(v_postApp_4216_, v___y_4217_, v___x_4238_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, lean_box(0));
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4241_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
v___x_4241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4212_, v_post_4213_, v_usedLetOnly_4214_, v_skipConstInApp_4215_, v_skipInstances_4211_, v_postApp_4216_, v_a_4240_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4241_;
}
else
{
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
return v___x_4239_;
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v_f_4228_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
v_a_4242_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4236_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4236_);
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
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_array_get_size(v_x_4219_);
lean_inc_ref(v_f_4228_);
v___x_4251_ = l_Lean_Meta_getFunInfoNArgs(v_f_4228_, v___x_4250_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v_paramInfo_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
v_paramInfo_4253_ = lean_ctor_get(v_a_4252_, 0);
lean_inc_ref(v_paramInfo_4253_);
lean_dec(v_a_4252_);
v___x_4254_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_4216_);
lean_inc_ref(v_post_4213_);
lean_inc_ref(v_pre_4212_);
v___x_4255_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4250_, v_paramInfo_4253_, v_pre_4212_, v_post_4213_, v_usedLetOnly_4214_, v_skipConstInApp_4215_, v_skipInstances_4211_, v_postApp_4216_, v___x_4254_, v_x_4219_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec_ref(v_paramInfo_4253_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = l_Lean_mkAppN(v_f_4228_, v_a_4256_);
lean_dec(v_a_4256_);
lean_inc_ref(v_postApp_4216_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc_ref(v___y_4230_);
v___x_4258_ = lean_apply_7(v_postApp_4216_, v___y_4217_, v___x_4257_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, lean_box(0));
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___x_4260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4212_, v_post_4213_, v_usedLetOnly_4214_, v_skipConstInApp_4215_, v_skipInstances_4211_, v_postApp_4216_, v_a_4259_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4260_;
}
else
{
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
return v___x_4258_;
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_f_4228_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
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
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_f_4228_);
lean_dec_ref(v_x_4219_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
v_a_4269_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4251_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4251_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
v___jp_4277_:
{
lean_object* v___x_4278_; 
lean_inc_ref(v_postApp_4216_);
lean_inc_ref(v_post_4213_);
lean_inc_ref(v_pre_4212_);
v___x_4278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4212_, v_post_4213_, v_usedLetOnly_4214_, v_skipConstInApp_4215_, v_skipInstances_4211_, v_postApp_4216_, v_x_4218_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
v_f_4228_ = v_a_4279_;
v___y_4229_ = v___y_4221_;
v___y_4230_ = v___y_4222_;
v___y_4231_ = v___y_4223_;
v___y_4232_ = v___y_4224_;
v___y_4233_ = v___y_4225_;
goto v___jp_4227_;
}
else
{
lean_dec_ref(v_x_4219_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v_postApp_4216_);
lean_dec_ref(v_post_4213_);
lean_dec_ref(v_pre_4212_);
return v___x_4278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4287_, lean_object* v_pre_4288_, lean_object* v_e_4289_, lean_object* v_post_4290_, uint8_t v_usedLetOnly_4291_, uint8_t v_skipConstInApp_4292_, uint8_t v_skipInstances_4293_, lean_object* v_postApp_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_Core_checkSystem(v___x_4287_, v___y_4298_, v___y_4299_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; 
lean_dec_ref_known(v___x_4301_, 1);
lean_inc_ref(v_pre_4288_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc_ref(v_e_4289_);
v___x_4302_ = lean_apply_6(v_pre_4288_, v_e_4289_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4351_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4351_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4351_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___y_4308_; 
switch(lean_obj_tag(v_a_4303_))
{
case 0:
{
lean_object* v_e_4343_; lean_object* v___x_4345_; 
lean_dec_ref(v_postApp_4294_);
lean_dec_ref(v_post_4290_);
lean_dec_ref(v_e_4289_);
lean_dec_ref(v_pre_4288_);
v_e_4343_ = lean_ctor_get(v_a_4303_, 0);
lean_inc_ref(v_e_4343_);
lean_dec_ref_known(v_a_4303_, 1);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v_e_4343_);
v___x_4345_ = v___x_4305_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_e_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
case 1:
{
lean_object* v_e_4347_; lean_object* v___x_4348_; 
lean_del_object(v___x_4305_);
lean_dec_ref(v_e_4289_);
v_e_4347_ = lean_ctor_get(v_a_4303_, 0);
lean_inc_ref(v_e_4347_);
lean_dec_ref_known(v_a_4303_, 1);
v___x_4348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v_e_4347_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4348_;
}
default: 
{
lean_object* v_e_x3f_4349_; 
lean_del_object(v___x_4305_);
v_e_x3f_4349_ = lean_ctor_get(v_a_4303_, 0);
lean_inc(v_e_x3f_4349_);
lean_dec_ref_known(v_a_4303_, 1);
if (lean_obj_tag(v_e_x3f_4349_) == 0)
{
v___y_4308_ = v_e_4289_;
goto v___jp_4307_;
}
else
{
lean_object* v_val_4350_; 
lean_dec_ref(v_e_4289_);
v_val_4350_ = lean_ctor_get(v_e_x3f_4349_, 0);
lean_inc(v_val_4350_);
lean_dec_ref_known(v_e_x3f_4349_, 1);
v___y_4308_ = v_val_4350_;
goto v___jp_4307_;
}
}
}
v___jp_4307_:
{
switch(lean_obj_tag(v___y_4308_))
{
case 7:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___x_4309_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4310_;
}
case 6:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___x_4311_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4312_;
}
case 8:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___closed__0));
v___x_4314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___x_4313_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4314_;
}
case 5:
{
lean_object* v_dummy_4315_; lean_object* v_nargs_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_dummy_4315_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4316_ = l_Lean_Expr_getAppNumArgs(v___y_4308_);
lean_inc(v_nargs_4316_);
v___x_4317_ = lean_mk_array(v_nargs_4316_, v_dummy_4315_);
v___x_4318_ = lean_unsigned_to_nat(1u);
v___x_4319_ = lean_nat_sub(v_nargs_4316_, v___x_4318_);
lean_dec(v_nargs_4316_);
lean_inc_ref(v___y_4308_);
v___x_4320_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4293_, v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_postApp_4294_, v___y_4308_, v___y_4308_, v___x_4317_, v___x_4319_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4320_;
}
case 10:
{
lean_object* v_data_4321_; lean_object* v_expr_4322_; lean_object* v___x_4323_; 
v_data_4321_ = lean_ctor_get(v___y_4308_, 0);
v_expr_4322_ = lean_ctor_get(v___y_4308_, 1);
lean_inc_ref(v_expr_4322_);
lean_inc_ref(v_postApp_4294_);
lean_inc_ref(v_post_4290_);
lean_inc_ref(v_pre_4288_);
v___x_4323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v_expr_4322_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; size_t v___x_4325_; size_t v___x_4326_; uint8_t v___x_4327_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v___x_4325_ = lean_ptr_addr(v_expr_4322_);
v___x_4326_ = lean_ptr_addr(v_a_4324_);
v___x_4327_ = lean_usize_dec_eq(v___x_4325_, v___x_4326_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
lean_inc(v_data_4321_);
lean_dec_ref_known(v___y_4308_, 2);
v___x_4328_ = l_Lean_Expr_mdata___override(v_data_4321_, v_a_4324_);
v___x_4329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___x_4328_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4329_;
}
else
{
lean_object* v___x_4330_; 
lean_dec(v_a_4324_);
v___x_4330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4330_;
}
}
else
{
lean_dec_ref_known(v___y_4308_, 2);
lean_dec_ref(v_postApp_4294_);
lean_dec_ref(v_post_4290_);
lean_dec_ref(v_pre_4288_);
return v___x_4323_;
}
}
case 11:
{
lean_object* v_typeName_4331_; lean_object* v_idx_4332_; lean_object* v_struct_4333_; lean_object* v___x_4334_; 
v_typeName_4331_ = lean_ctor_get(v___y_4308_, 0);
v_idx_4332_ = lean_ctor_get(v___y_4308_, 1);
v_struct_4333_ = lean_ctor_get(v___y_4308_, 2);
lean_inc_ref(v_struct_4333_);
lean_inc_ref(v_postApp_4294_);
lean_inc_ref(v_post_4290_);
lean_inc_ref(v_pre_4288_);
v___x_4334_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v_struct_4333_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; size_t v___x_4336_; size_t v___x_4337_; uint8_t v___x_4338_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v___x_4336_ = lean_ptr_addr(v_struct_4333_);
v___x_4337_ = lean_ptr_addr(v_a_4335_);
v___x_4338_ = lean_usize_dec_eq(v___x_4336_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_inc(v_idx_4332_);
lean_inc(v_typeName_4331_);
lean_dec_ref_known(v___y_4308_, 3);
v___x_4339_ = l_Lean_Expr_proj___override(v_typeName_4331_, v_idx_4332_, v_a_4335_);
v___x_4340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___x_4339_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; 
lean_dec(v_a_4335_);
v___x_4341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4341_;
}
}
else
{
lean_dec_ref_known(v___y_4308_, 3);
lean_dec_ref(v_postApp_4294_);
lean_dec_ref(v_post_4290_);
lean_dec_ref(v_pre_4288_);
return v___x_4334_;
}
}
default: 
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4288_, v_post_4290_, v_usedLetOnly_4291_, v_skipConstInApp_4292_, v_skipInstances_4293_, v_postApp_4294_, v___y_4308_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4342_;
}
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v_postApp_4294_);
lean_dec_ref(v_post_4290_);
lean_dec_ref(v_e_4289_);
lean_dec_ref(v_pre_4288_);
v_a_4352_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4302_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4302_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec_ref(v_postApp_4294_);
lean_dec_ref(v_post_4290_);
lean_dec_ref(v_e_4289_);
lean_dec_ref(v_pre_4288_);
v_a_4360_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4301_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4301_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4368_, lean_object* v_pre_4369_, lean_object* v_e_4370_, lean_object* v_post_4371_, lean_object* v_usedLetOnly_4372_, lean_object* v_skipConstInApp_4373_, lean_object* v_skipInstances_4374_, lean_object* v_postApp_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
uint8_t v_usedLetOnly_boxed_4382_; uint8_t v_skipConstInApp_boxed_4383_; uint8_t v_skipInstances_boxed_4384_; lean_object* v_res_4385_; 
v_usedLetOnly_boxed_4382_ = lean_unbox(v_usedLetOnly_4372_);
v_skipConstInApp_boxed_4383_ = lean_unbox(v_skipConstInApp_4373_);
v_skipInstances_boxed_4384_ = lean_unbox(v_skipInstances_4374_);
v_res_4385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4368_, v_pre_4369_, v_e_4370_, v_post_4371_, v_usedLetOnly_boxed_4382_, v_skipConstInApp_boxed_4383_, v_skipInstances_boxed_4384_, v_postApp_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4386_, lean_object* v_post_4387_, uint8_t v_usedLetOnly_4388_, uint8_t v_skipConstInApp_4389_, uint8_t v_skipInstances_4390_, lean_object* v_postApp_4391_, lean_object* v_e_4392_, lean_object* v_a_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_inc(v_a_4393_);
v___x_4399_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4399_, 0, lean_box(0));
lean_closure_set(v___x_4399_, 1, lean_box(0));
lean_closure_set(v___x_4399_, 2, v_a_4393_);
v___x_4400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4399_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4435_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4435_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4435_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4401_, v_e_4392_);
lean_dec(v_a_4401_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; 
lean_del_object(v___x_4403_);
v___x_4406_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4407_ = lean_box(v_usedLetOnly_4388_);
v___x_4408_ = lean_box(v_skipConstInApp_4389_);
v___x_4409_ = lean_box(v_skipInstances_4390_);
lean_inc_ref(v_e_4392_);
v___f_4410_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4410_, 0, v___x_4406_);
lean_closure_set(v___f_4410_, 1, v_pre_4386_);
lean_closure_set(v___f_4410_, 2, v_e_4392_);
lean_closure_set(v___f_4410_, 3, v_post_4387_);
lean_closure_set(v___f_4410_, 4, v___x_4407_);
lean_closure_set(v___f_4410_, 5, v___x_4408_);
lean_closure_set(v___f_4410_, 6, v___x_4409_);
lean_closure_set(v___f_4410_, 7, v_postApp_4391_);
v___x_4411_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4410_, v_a_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___f_4413_; lean_object* v___x_4414_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc_n(v_a_4412_, 2);
lean_dec_ref_known(v___x_4411_, 1);
lean_inc(v_a_4393_);
v___f_4413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4413_, 0, v_a_4393_);
lean_closure_set(v___f_4413_, 1, v_e_4392_);
lean_closure_set(v___f_4413_, 2, v_a_4412_);
v___x_4414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4413_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v___x_4414_, 0);
lean_dec(v_unused_4422_);
v___x_4416_ = v___x_4414_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v___x_4414_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v_a_4412_);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4412_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4412_);
v_a_4423_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4414_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4414_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
lean_dec_ref(v_e_4392_);
return v___x_4411_;
}
}
else
{
lean_object* v_val_4431_; lean_object* v___x_4433_; 
lean_dec_ref(v_e_4392_);
lean_dec_ref(v_postApp_4391_);
lean_dec_ref(v_post_4387_);
lean_dec_ref(v_pre_4386_);
v_val_4431_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_val_4431_);
lean_dec_ref_known(v___x_4405_, 1);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_val_4431_);
v___x_4433_ = v___x_4403_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_val_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec_ref(v_e_4392_);
lean_dec_ref(v_postApp_4391_);
lean_dec_ref(v_post_4387_);
lean_dec_ref(v_pre_4386_);
v_a_4436_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4400_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4400_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4444_, lean_object* v_post_4445_, uint8_t v_usedLetOnly_4446_, uint8_t v_skipConstInApp_4447_, uint8_t v_skipInstances_4448_, lean_object* v_postApp_4449_, lean_object* v_fvars_4450_, lean_object* v_e_4451_, lean_object* v_a_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
if (lean_obj_tag(v_e_4451_) == 7)
{
lean_object* v_binderName_4458_; lean_object* v_binderType_4459_; lean_object* v_body_4460_; uint8_t v_binderInfo_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___f_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_binderName_4458_ = lean_ctor_get(v_e_4451_, 0);
lean_inc(v_binderName_4458_);
v_binderType_4459_ = lean_ctor_get(v_e_4451_, 1);
lean_inc_ref(v_binderType_4459_);
v_body_4460_ = lean_ctor_get(v_e_4451_, 2);
lean_inc_ref(v_body_4460_);
v_binderInfo_4461_ = lean_ctor_get_uint8(v_e_4451_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4451_, 3);
v___x_4462_ = lean_box(v_usedLetOnly_4446_);
v___x_4463_ = lean_box(v_skipConstInApp_4447_);
v___x_4464_ = lean_box(v_skipInstances_4448_);
lean_inc_ref(v_postApp_4449_);
lean_inc_ref(v_post_4445_);
lean_inc_ref(v_pre_4444_);
lean_inc_ref(v_fvars_4450_);
v___f_4465_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 15, 8);
lean_closure_set(v___f_4465_, 0, v_fvars_4450_);
lean_closure_set(v___f_4465_, 1, v_pre_4444_);
lean_closure_set(v___f_4465_, 2, v_post_4445_);
lean_closure_set(v___f_4465_, 3, v___x_4462_);
lean_closure_set(v___f_4465_, 4, v___x_4463_);
lean_closure_set(v___f_4465_, 5, v___x_4464_);
lean_closure_set(v___f_4465_, 6, v_postApp_4449_);
lean_closure_set(v___f_4465_, 7, v_body_4460_);
v___x_4466_ = lean_expr_instantiate_rev(v_binderType_4459_, v_fvars_4450_);
lean_dec_ref(v_fvars_4450_);
lean_dec_ref(v_binderType_4459_);
v___x_4467_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4444_, v_post_4445_, v_usedLetOnly_4446_, v_skipConstInApp_4447_, v_skipInstances_4448_, v_postApp_4449_, v___x_4466_, v_a_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref_known(v___x_4467_, 1);
v___x_4469_ = 0;
v___x_4470_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4458_, v_binderInfo_4461_, v_a_4468_, v___f_4465_, v___x_4469_, v_a_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4470_;
}
else
{
lean_dec_ref(v___f_4465_);
lean_dec(v_binderName_4458_);
return v___x_4467_;
}
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = lean_expr_instantiate_rev(v_e_4451_, v_fvars_4450_);
lean_dec_ref(v_e_4451_);
lean_inc_ref(v_postApp_4449_);
lean_inc_ref(v_post_4445_);
lean_inc_ref(v_pre_4444_);
v___x_4472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4444_, v_post_4445_, v_usedLetOnly_4446_, v_skipConstInApp_4447_, v_skipInstances_4448_, v_postApp_4449_, v___x_4471_, v_a_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; uint8_t v___x_4474_; uint8_t v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4474_ = 0;
v___x_4475_ = 1;
v___x_4476_ = 1;
v___x_4477_ = l_Lean_Meta_mkForallFVars(v_fvars_4450_, v_a_4473_, v___x_4474_, v_usedLetOnly_4446_, v___x_4475_, v___x_4476_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec_ref(v_fvars_4450_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v___x_4479_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4444_, v_post_4445_, v_usedLetOnly_4446_, v_skipConstInApp_4447_, v_skipInstances_4448_, v_postApp_4449_, v_a_4478_, v_a_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4479_;
}
else
{
lean_dec_ref(v_postApp_4449_);
lean_dec_ref(v_post_4445_);
lean_dec_ref(v_pre_4444_);
return v___x_4477_;
}
}
else
{
lean_dec_ref(v_fvars_4450_);
lean_dec_ref(v_postApp_4449_);
lean_dec_ref(v_post_4445_);
lean_dec_ref(v_pre_4444_);
return v___x_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4480_, lean_object* v_pre_4481_, lean_object* v_post_4482_, uint8_t v_usedLetOnly_4483_, uint8_t v_skipConstInApp_4484_, uint8_t v_skipInstances_4485_, lean_object* v_postApp_4486_, lean_object* v_body_4487_, lean_object* v_x_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_array_push(v_fvars_4480_, v_x_4488_);
v___x_4496_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4481_, v_post_4482_, v_usedLetOnly_4483_, v_skipConstInApp_4484_, v_skipInstances_4485_, v_postApp_4486_, v___x_4495_, v_body_4487_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4497_, lean_object* v_post_4498_, lean_object* v_usedLetOnly_4499_, lean_object* v_skipConstInApp_4500_, lean_object* v_skipInstances_4501_, lean_object* v_postApp_4502_, lean_object* v_e_4503_, lean_object* v_a_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v_usedLetOnly_boxed_4510_; uint8_t v_skipConstInApp_boxed_4511_; uint8_t v_skipInstances_boxed_4512_; lean_object* v_res_4513_; 
v_usedLetOnly_boxed_4510_ = lean_unbox(v_usedLetOnly_4499_);
v_skipConstInApp_boxed_4511_ = lean_unbox(v_skipConstInApp_4500_);
v_skipInstances_boxed_4512_ = lean_unbox(v_skipInstances_4501_);
v_res_4513_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4497_, v_post_4498_, v_usedLetOnly_boxed_4510_, v_skipConstInApp_boxed_4511_, v_skipInstances_boxed_4512_, v_postApp_4502_, v_e_4503_, v_a_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v_a_4504_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4514_, lean_object* v_post_4515_, lean_object* v_usedLetOnly_4516_, lean_object* v_skipConstInApp_4517_, lean_object* v_skipInstances_4518_, lean_object* v_postApp_4519_, lean_object* v_sz_4520_, lean_object* v_i_4521_, lean_object* v_bs_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v_usedLetOnly_boxed_4529_; uint8_t v_skipConstInApp_boxed_4530_; uint8_t v_skipInstances_boxed_4531_; size_t v_sz_boxed_4532_; size_t v_i_boxed_4533_; lean_object* v_res_4534_; 
v_usedLetOnly_boxed_4529_ = lean_unbox(v_usedLetOnly_4516_);
v_skipConstInApp_boxed_4530_ = lean_unbox(v_skipConstInApp_4517_);
v_skipInstances_boxed_4531_ = lean_unbox(v_skipInstances_4518_);
v_sz_boxed_4532_ = lean_unbox_usize(v_sz_4520_);
lean_dec(v_sz_4520_);
v_i_boxed_4533_ = lean_unbox_usize(v_i_4521_);
lean_dec(v_i_4521_);
v_res_4534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4514_, v_post_4515_, v_usedLetOnly_boxed_4529_, v_skipConstInApp_boxed_4530_, v_skipInstances_boxed_4531_, v_postApp_4519_, v_sz_boxed_4532_, v_i_boxed_4533_, v_bs_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4535_, lean_object* v_post_4536_, lean_object* v_usedLetOnly_4537_, lean_object* v_skipConstInApp_4538_, lean_object* v_skipInstances_4539_, lean_object* v_postApp_4540_, lean_object* v_e_4541_, lean_object* v_a_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_usedLetOnly_boxed_4548_; uint8_t v_skipConstInApp_boxed_4549_; uint8_t v_skipInstances_boxed_4550_; lean_object* v_res_4551_; 
v_usedLetOnly_boxed_4548_ = lean_unbox(v_usedLetOnly_4537_);
v_skipConstInApp_boxed_4549_ = lean_unbox(v_skipConstInApp_4538_);
v_skipInstances_boxed_4550_ = lean_unbox(v_skipInstances_4539_);
v_res_4551_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4535_, v_post_4536_, v_usedLetOnly_boxed_4548_, v_skipConstInApp_boxed_4549_, v_skipInstances_boxed_4550_, v_postApp_4540_, v_e_4541_, v_a_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v_a_4542_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4552_, lean_object* v_post_4553_, lean_object* v_usedLetOnly_4554_, lean_object* v_skipConstInApp_4555_, lean_object* v_skipInstances_4556_, lean_object* v_postApp_4557_, lean_object* v_fvars_4558_, lean_object* v_e_4559_, lean_object* v_a_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
uint8_t v_usedLetOnly_boxed_4566_; uint8_t v_skipConstInApp_boxed_4567_; uint8_t v_skipInstances_boxed_4568_; lean_object* v_res_4569_; 
v_usedLetOnly_boxed_4566_ = lean_unbox(v_usedLetOnly_4554_);
v_skipConstInApp_boxed_4567_ = lean_unbox(v_skipConstInApp_4555_);
v_skipInstances_boxed_4568_ = lean_unbox(v_skipInstances_4556_);
v_res_4569_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4552_, v_post_4553_, v_usedLetOnly_boxed_4566_, v_skipConstInApp_boxed_4567_, v_skipInstances_boxed_4568_, v_postApp_4557_, v_fvars_4558_, v_e_4559_, v_a_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v_a_4560_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4570_, lean_object* v_post_4571_, lean_object* v_usedLetOnly_4572_, lean_object* v_skipConstInApp_4573_, lean_object* v_skipInstances_4574_, lean_object* v_postApp_4575_, lean_object* v_fvars_4576_, lean_object* v_e_4577_, lean_object* v_a_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
uint8_t v_usedLetOnly_boxed_4584_; uint8_t v_skipConstInApp_boxed_4585_; uint8_t v_skipInstances_boxed_4586_; lean_object* v_res_4587_; 
v_usedLetOnly_boxed_4584_ = lean_unbox(v_usedLetOnly_4572_);
v_skipConstInApp_boxed_4585_ = lean_unbox(v_skipConstInApp_4573_);
v_skipInstances_boxed_4586_ = lean_unbox(v_skipInstances_4574_);
v_res_4587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4570_, v_post_4571_, v_usedLetOnly_boxed_4584_, v_skipConstInApp_boxed_4585_, v_skipInstances_boxed_4586_, v_postApp_4575_, v_fvars_4576_, v_e_4577_, v_a_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v_a_4578_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4588_, lean_object* v_post_4589_, lean_object* v_usedLetOnly_4590_, lean_object* v_skipConstInApp_4591_, lean_object* v_skipInstances_4592_, lean_object* v_postApp_4593_, lean_object* v_fvars_4594_, lean_object* v_e_4595_, lean_object* v_a_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
uint8_t v_usedLetOnly_boxed_4602_; uint8_t v_skipConstInApp_boxed_4603_; uint8_t v_skipInstances_boxed_4604_; lean_object* v_res_4605_; 
v_usedLetOnly_boxed_4602_ = lean_unbox(v_usedLetOnly_4590_);
v_skipConstInApp_boxed_4603_ = lean_unbox(v_skipConstInApp_4591_);
v_skipInstances_boxed_4604_ = lean_unbox(v_skipInstances_4592_);
v_res_4605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4588_, v_post_4589_, v_usedLetOnly_boxed_4602_, v_skipConstInApp_boxed_4603_, v_skipInstances_boxed_4604_, v_postApp_4593_, v_fvars_4594_, v_e_4595_, v_a_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v_a_4596_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4606_, lean_object* v___x_4607_, lean_object* v_pre_4608_, lean_object* v_post_4609_, lean_object* v_usedLetOnly_4610_, lean_object* v_skipConstInApp_4611_, lean_object* v_skipInstances_4612_, lean_object* v_postApp_4613_, lean_object* v_a_4614_, lean_object* v_b_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v_usedLetOnly_boxed_4622_; uint8_t v_skipConstInApp_boxed_4623_; uint8_t v_skipInstances_boxed_4624_; lean_object* v_res_4625_; 
v_usedLetOnly_boxed_4622_ = lean_unbox(v_usedLetOnly_4610_);
v_skipConstInApp_boxed_4623_ = lean_unbox(v_skipConstInApp_4611_);
v_skipInstances_boxed_4624_ = lean_unbox(v_skipInstances_4612_);
v_res_4625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4606_, v___x_4607_, v_pre_4608_, v_post_4609_, v_usedLetOnly_boxed_4622_, v_skipConstInApp_boxed_4623_, v_skipInstances_boxed_4624_, v_postApp_4613_, v_a_4614_, v_b_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___x_4607_);
lean_dec(v_upperBound_4606_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4626_, lean_object* v_pre_4627_, lean_object* v_post_4628_, lean_object* v_usedLetOnly_4629_, lean_object* v_skipConstInApp_4630_, lean_object* v_postApp_4631_, lean_object* v___y_4632_, lean_object* v_x_4633_, lean_object* v_x_4634_, lean_object* v_x_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
uint8_t v_skipInstances_boxed_4642_; uint8_t v_usedLetOnly_boxed_4643_; uint8_t v_skipConstInApp_boxed_4644_; lean_object* v_res_4645_; 
v_skipInstances_boxed_4642_ = lean_unbox(v_skipInstances_4626_);
v_usedLetOnly_boxed_4643_ = lean_unbox(v_usedLetOnly_4629_);
v_skipConstInApp_boxed_4644_ = lean_unbox(v_skipConstInApp_4630_);
v_res_4645_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4642_, v_pre_4627_, v_post_4628_, v_usedLetOnly_boxed_4643_, v_skipConstInApp_boxed_4644_, v_postApp_4631_, v___y_4632_, v_x_4633_, v_x_4634_, v_x_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1(lean_object* v_x_4646_, lean_object* v_e_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_e_4647_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1___boxed(lean_object* v_x_4654_, lean_object* v_e_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__1(v_x_4654_, v_e_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v_x_4654_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4663_, lean_object* v_pre_4664_, lean_object* v_post_4665_, uint8_t v_usedLetOnly_4666_, uint8_t v_skipConstInApp_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___f_4673_; uint8_t v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v_a_4677_; lean_object* v___x_4678_; 
v___f_4673_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___closed__0));
v___x_4674_ = 0;
v___x_4675_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4676_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4675_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref(v___x_4676_);
v___x_4678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4664_, v_post_4665_, v_usedLetOnly_4666_, v_skipConstInApp_4667_, v___x_4674_, v___f_4673_, v_input_4663_, v_a_4677_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v___x_4680_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4680_, 0, lean_box(0));
lean_closure_set(v___x_4680_, 1, lean_box(0));
lean_closure_set(v___x_4680_, 2, v_a_4677_);
v___x_4681_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4680_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4688_ == 0)
{
lean_object* v_unused_4689_; 
v_unused_4689_ = lean_ctor_get(v___x_4681_, 0);
lean_dec(v_unused_4689_);
v___x_4683_ = v___x_4681_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_dec(v___x_4681_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 0, v_a_4679_);
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4679_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
else
{
lean_dec(v_a_4677_);
return v___x_4678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4690_, lean_object* v_pre_4691_, lean_object* v_post_4692_, lean_object* v_usedLetOnly_4693_, lean_object* v_skipConstInApp_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
uint8_t v_usedLetOnly_boxed_4700_; uint8_t v_skipConstInApp_boxed_4701_; lean_object* v_res_4702_; 
v_usedLetOnly_boxed_4700_ = lean_unbox(v_usedLetOnly_4693_);
v_skipConstInApp_boxed_4701_ = lean_unbox(v_skipConstInApp_4694_);
v_res_4702_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4690_, v_pre_4691_, v_post_4692_, v_usedLetOnly_boxed_4700_, v_skipConstInApp_boxed_4701_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4704_, uint8_t v_zetaDelta_4705_, uint8_t v_zetaHave_4706_, uint8_t v_beta_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v_lctx_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___f_4717_; uint8_t v___x_4718_; 
v_lctx_4713_ = lean_ctor_get(v_a_4708_, 2);
lean_inc_ref(v_lctx_4713_);
v___x_4714_ = lean_local_ctx_num_indices(v_lctx_4713_);
v___x_4715_ = lean_box(v_zetaHave_4706_);
v___x_4716_ = lean_box(v_zetaDelta_4705_);
v___f_4717_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4717_, 0, v___x_4715_);
lean_closure_set(v___f_4717_, 1, v___x_4714_);
lean_closure_set(v___f_4717_, 2, v___x_4716_);
v___x_4718_ = 1;
if (v_beta_4707_ == 0)
{
lean_object* v___f_4719_; lean_object* v___f_4720_; lean_object* v___x_4721_; 
v___f_4719_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4720_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4720_, 0, v___f_4717_);
v___x_4721_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4704_, v___f_4720_, v___f_4719_, v___x_4718_, v_beta_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v___x_4721_;
}
else
{
lean_object* v___f_4722_; lean_object* v___f_4723_; uint8_t v___x_4724_; lean_object* v___x_4725_; 
v___f_4722_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4723_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4723_, 0, v___f_4717_);
v___x_4724_ = 0;
v___x_4725_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4704_, v___f_4723_, v___f_4722_, v___x_4718_, v___x_4724_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v___x_4725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4726_, lean_object* v_zetaDelta_4727_, lean_object* v_zetaHave_4728_, lean_object* v_beta_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
uint8_t v_zetaDelta_boxed_4735_; uint8_t v_zetaHave_boxed_4736_; uint8_t v_beta_boxed_4737_; lean_object* v_res_4738_; 
v_zetaDelta_boxed_4735_ = lean_unbox(v_zetaDelta_4727_);
v_zetaHave_boxed_4736_ = lean_unbox(v_zetaHave_4728_);
v_beta_boxed_4737_ = lean_unbox(v_beta_4729_);
v_res_4738_ = l_Lean_Meta_zetaReduce(v_e_4726_, v_zetaDelta_boxed_4735_, v_zetaHave_boxed_4736_, v_beta_boxed_4737_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4739_, lean_object* v___x_4740_, lean_object* v_pre_4741_, lean_object* v_post_4742_, uint8_t v_usedLetOnly_4743_, uint8_t v_skipConstInApp_4744_, uint8_t v_skipInstances_4745_, lean_object* v_postApp_4746_, lean_object* v___x_4747_, lean_object* v_inst_4748_, lean_object* v_R_4749_, lean_object* v_a_4750_, lean_object* v_b_4751_, lean_object* v_c_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4739_, v___x_4740_, v_pre_4741_, v_post_4742_, v_usedLetOnly_4743_, v_skipConstInApp_4744_, v_skipInstances_4745_, v_postApp_4746_, v_a_4750_, v_b_4751_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4760_ = _args[0];
lean_object* v___x_4761_ = _args[1];
lean_object* v_pre_4762_ = _args[2];
lean_object* v_post_4763_ = _args[3];
lean_object* v_usedLetOnly_4764_ = _args[4];
lean_object* v_skipConstInApp_4765_ = _args[5];
lean_object* v_skipInstances_4766_ = _args[6];
lean_object* v_postApp_4767_ = _args[7];
lean_object* v___x_4768_ = _args[8];
lean_object* v_inst_4769_ = _args[9];
lean_object* v_R_4770_ = _args[10];
lean_object* v_a_4771_ = _args[11];
lean_object* v_b_4772_ = _args[12];
lean_object* v_c_4773_ = _args[13];
lean_object* v___y_4774_ = _args[14];
lean_object* v___y_4775_ = _args[15];
lean_object* v___y_4776_ = _args[16];
lean_object* v___y_4777_ = _args[17];
lean_object* v___y_4778_ = _args[18];
lean_object* v___y_4779_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_4780_; uint8_t v_skipConstInApp_boxed_4781_; uint8_t v_skipInstances_boxed_4782_; lean_object* v_res_4783_; 
v_usedLetOnly_boxed_4780_ = lean_unbox(v_usedLetOnly_4764_);
v_skipConstInApp_boxed_4781_ = lean_unbox(v_skipConstInApp_4765_);
v_skipInstances_boxed_4782_ = lean_unbox(v_skipInstances_4766_);
v_res_4783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4760_, v___x_4761_, v_pre_4762_, v_post_4763_, v_usedLetOnly_boxed_4780_, v_skipConstInApp_boxed_4781_, v_skipInstances_boxed_4782_, v_postApp_4767_, v___x_4768_, v_inst_4769_, v_R_4770_, v_a_4771_, v_b_4772_, v_c_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec(v___x_4768_);
lean_dec_ref(v___x_4761_);
lean_dec(v_upperBound_4760_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4784_, lean_object* v_name_4785_, uint8_t v_bi_4786_, lean_object* v_type_4787_, lean_object* v_k_4788_, uint8_t v_kind_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4785_, v_bi_4786_, v_type_4787_, v_k_4788_, v_kind_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4797_, lean_object* v_name_4798_, lean_object* v_bi_4799_, lean_object* v_type_4800_, lean_object* v_k_4801_, lean_object* v_kind_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
uint8_t v_bi_boxed_4809_; uint8_t v_kind_boxed_4810_; lean_object* v_res_4811_; 
v_bi_boxed_4809_ = lean_unbox(v_bi_4799_);
v_kind_boxed_4810_ = lean_unbox(v_kind_4802_);
v_res_4811_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4797_, v_name_4798_, v_bi_boxed_4809_, v_type_4800_, v_k_4801_, v_kind_boxed_4810_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4812_, lean_object* v_name_4813_, lean_object* v_type_4814_, lean_object* v_val_4815_, lean_object* v_k_4816_, uint8_t v_nondep_4817_, uint8_t v_kind_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4813_, v_type_4814_, v_val_4815_, v_k_4816_, v_nondep_4817_, v_kind_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4826_, lean_object* v_name_4827_, lean_object* v_type_4828_, lean_object* v_val_4829_, lean_object* v_k_4830_, lean_object* v_nondep_4831_, lean_object* v_kind_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
uint8_t v_nondep_boxed_4839_; uint8_t v_kind_boxed_4840_; lean_object* v_res_4841_; 
v_nondep_boxed_4839_ = lean_unbox(v_nondep_4831_);
v_kind_boxed_4840_ = lean_unbox(v_kind_4832_);
v_res_4841_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4826_, v_name_4827_, v_type_4828_, v_val_4829_, v_k_4830_, v_nondep_boxed_4839_, v_kind_boxed_4840_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4842_, lean_object* v_ref_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4843_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_ref_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4850_, v_ref_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4858_, lean_object* v_x_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4867_, lean_object* v_x_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4867_, v_x_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
return v_res_4875_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4876_, lean_object* v_as_4877_, size_t v_i_4878_, size_t v_stop_4879_){
_start:
{
uint8_t v___x_4880_; 
v___x_4880_ = lean_usize_dec_eq(v_i_4878_, v_stop_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; uint8_t v___x_4882_; 
v___x_4881_ = lean_array_uget_borrowed(v_as_4877_, v_i_4878_);
v___x_4882_ = l_Lean_instBEqFVarId_beq(v_a_4876_, v___x_4881_);
if (v___x_4882_ == 0)
{
size_t v___x_4883_; size_t v___x_4884_; 
v___x_4883_ = ((size_t)1ULL);
v___x_4884_ = lean_usize_add(v_i_4878_, v___x_4883_);
v_i_4878_ = v___x_4884_;
goto _start;
}
else
{
return v___x_4882_;
}
}
else
{
uint8_t v___x_4886_; 
v___x_4886_ = 0;
return v___x_4886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4887_, lean_object* v_as_4888_, lean_object* v_i_4889_, lean_object* v_stop_4890_){
_start:
{
size_t v_i_boxed_4891_; size_t v_stop_boxed_4892_; uint8_t v_res_4893_; lean_object* v_r_4894_; 
v_i_boxed_4891_ = lean_unbox_usize(v_i_4889_);
lean_dec(v_i_4889_);
v_stop_boxed_4892_ = lean_unbox_usize(v_stop_4890_);
lean_dec(v_stop_4890_);
v_res_4893_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4887_, v_as_4888_, v_i_boxed_4891_, v_stop_boxed_4892_);
lean_dec_ref(v_as_4888_);
lean_dec(v_a_4887_);
v_r_4894_ = lean_box(v_res_4893_);
return v_r_4894_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
v___x_4897_ = lean_unsigned_to_nat(0u);
v___x_4898_ = lean_array_get_size(v_as_4895_);
v___x_4899_ = lean_nat_dec_lt(v___x_4897_, v___x_4898_);
if (v___x_4899_ == 0)
{
return v___x_4899_;
}
else
{
size_t v___x_4900_; size_t v___x_4901_; uint8_t v___x_4902_; 
v___x_4900_ = ((size_t)0ULL);
v___x_4901_ = lean_usize_of_nat(v___x_4898_);
v___x_4902_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4896_, v_as_4895_, v___x_4900_, v___x_4901_);
return v___x_4902_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4903_, lean_object* v_a_4904_){
_start:
{
uint8_t v_res_4905_; lean_object* v_r_4906_; 
v_res_4905_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4903_, v_a_4904_);
lean_dec(v_a_4904_);
lean_dec_ref(v_as_4903_);
v_r_4906_ = lean_box(v_res_4905_);
return v_r_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4907_, lean_object* v_e_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Expr_getAppFn(v_e_4908_);
if (lean_obj_tag(v___x_4917_) == 1)
{
lean_object* v_fvarId_4918_; uint8_t v___x_4919_; 
v_fvarId_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_fvarId_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v___x_4919_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4907_, v_fvarId_4918_);
if (v___x_4919_ == 0)
{
lean_dec(v_fvarId_4918_);
lean_dec_ref(v_e_4908_);
goto v___jp_4914_;
}
else
{
uint8_t v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = 0;
v___x_4921_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4918_, v___x_4920_, v___y_4909_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
if (lean_obj_tag(v_a_4922_) == 1)
{
lean_object* v_val_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4946_; 
v_val_4923_ = lean_ctor_get(v_a_4922_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_a_4922_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4925_ = v_a_4922_;
v_isShared_4926_ = v_isSharedCheck_4946_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_val_4923_);
lean_dec(v_a_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4946_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4945_; 
v___x_4927_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4923_, v___y_4910_);
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4945_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4945_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v_dummy_4932_; lean_object* v_nargs_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
v_dummy_4932_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4933_ = l_Lean_Expr_getAppNumArgs(v_e_4908_);
lean_inc(v_nargs_4933_);
v___x_4934_ = lean_mk_array(v_nargs_4933_, v_dummy_4932_);
v___x_4935_ = lean_unsigned_to_nat(1u);
v___x_4936_ = lean_nat_sub(v_nargs_4933_, v___x_4935_);
lean_dec(v_nargs_4933_);
v___x_4937_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4908_, v___x_4934_, v___x_4936_);
v___x_4938_ = l_Lean_Expr_beta(v_a_4928_, v___x_4937_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4938_);
v___x_4940_ = v___x_4925_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4942_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4940_);
v___x_4942_ = v___x_4930_;
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
}
else
{
lean_dec(v_a_4922_);
lean_dec_ref(v_e_4908_);
goto v___jp_4914_;
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec_ref(v_e_4908_);
v_a_4947_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4921_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4921_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec_ref(v___x_4917_);
lean_dec_ref(v_e_4908_);
v___x_4955_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
return v___x_4956_;
}
v___jp_4914_:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4915_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
return v___x_4916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4957_, lean_object* v_e_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4957_, v_e_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec_ref(v_fvars_4957_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4965_, lean_object* v_fvars_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___f_4972_; lean_object* v_pre_4973_; uint8_t v___x_4974_; lean_object* v___x_4975_; 
v___f_4972_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4973_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4973_, 0, v_fvars_4966_);
v___x_4974_ = 0;
v___x_4975_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4965_, v_pre_4973_, v___f_4972_, v___x_4974_, v___x_4974_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4976_, lean_object* v_fvars_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Meta_zetaDeltaFVars(v_e_4976_, v_fvars_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
return v_res_4983_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4984_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4985_);
return v___x_4986_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4987_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v___x_4992_; lean_object* v_nextMacroScope_4993_; lean_object* v_ngen_4994_; lean_object* v_auxDeclNGen_4995_; lean_object* v_traceState_4996_; lean_object* v_recordedDeps_4997_; lean_object* v_messages_4998_; lean_object* v_infoState_4999_; lean_object* v_snapshotTasks_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5011_; 
v___x_4992_ = lean_st_ref_take(v___y_4990_);
v_nextMacroScope_4993_ = lean_ctor_get(v___x_4992_, 1);
v_ngen_4994_ = lean_ctor_get(v___x_4992_, 2);
v_auxDeclNGen_4995_ = lean_ctor_get(v___x_4992_, 3);
v_traceState_4996_ = lean_ctor_get(v___x_4992_, 4);
v_recordedDeps_4997_ = lean_ctor_get(v___x_4992_, 6);
v_messages_4998_ = lean_ctor_get(v___x_4992_, 7);
v_infoState_4999_ = lean_ctor_get(v___x_4992_, 8);
v_snapshotTasks_5000_ = lean_ctor_get(v___x_4992_, 9);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5011_ == 0)
{
lean_object* v_unused_5012_; lean_object* v_unused_5013_; 
v_unused_5012_ = lean_ctor_get(v___x_4992_, 5);
lean_dec(v_unused_5012_);
v_unused_5013_ = lean_ctor_get(v___x_4992_, 0);
lean_dec(v_unused_5013_);
v___x_5002_ = v___x_4992_;
v_isShared_5003_ = v_isSharedCheck_5011_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_snapshotTasks_5000_);
lean_inc(v_infoState_4999_);
lean_inc(v_messages_4998_);
lean_inc(v_recordedDeps_4997_);
lean_inc(v_traceState_4996_);
lean_inc(v_auxDeclNGen_4995_);
lean_inc(v_ngen_4994_);
lean_inc(v_nextMacroScope_4993_);
lean_dec(v___x_4992_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5011_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5004_ = lean_box(0);
v___x_5005_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 5, v___x_5005_);
lean_ctor_set(v___x_5002_, 0, v_env_4989_);
v___x_5007_ = v___x_5002_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_env_4989_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_nextMacroScope_4993_);
lean_ctor_set(v_reuseFailAlloc_5010_, 2, v_ngen_4994_);
lean_ctor_set(v_reuseFailAlloc_5010_, 3, v_auxDeclNGen_4995_);
lean_ctor_set(v_reuseFailAlloc_5010_, 4, v_traceState_4996_);
lean_ctor_set(v_reuseFailAlloc_5010_, 5, v___x_5005_);
lean_ctor_set(v_reuseFailAlloc_5010_, 6, v_recordedDeps_4997_);
lean_ctor_set(v_reuseFailAlloc_5010_, 7, v_messages_4998_);
lean_ctor_set(v_reuseFailAlloc_5010_, 8, v_infoState_4999_);
lean_ctor_set(v_reuseFailAlloc_5010_, 9, v_snapshotTasks_5000_);
v___x_5007_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = lean_st_ref_put(v___y_4990_, v___x_5007_);
v___x_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5004_);
return v___x_5009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5014_, v___y_5015_);
lean_dec(v___y_5015_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5018_, v___y_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_5028_, lean_object* v___x_5029_, uint8_t v___x_5030_, lean_object* v_e_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
if (lean_obj_tag(v_e_5031_) == 4)
{
lean_object* v_declName_5035_; lean_object* v_us_5036_; uint8_t v___x_5037_; uint8_t v___x_5038_; 
v_declName_5035_ = lean_ctor_get(v_e_5031_, 0);
v_us_5036_ = lean_ctor_get(v_e_5031_, 1);
v___x_5037_ = 1;
lean_inc(v_declName_5035_);
v___x_5038_ = l_Lean_Environment_contains(v_env_5028_, v_declName_5035_, v___x_5037_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; 
lean_inc(v_declName_5035_);
v___x_5039_ = l_Lean_Environment_find_x3f(v___x_5029_, v_declName_5035_, v___x_5030_);
if (lean_obj_tag(v___x_5039_) == 1)
{
lean_object* v_val_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5069_; 
v_val_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5069_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_val_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5069_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
uint8_t v___x_5044_; 
v___x_5044_ = l_Lean_ConstantInfo_hasValue(v_val_5040_, v___x_5037_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5046_; 
lean_dec(v_val_5040_);
if (v_isShared_5043_ == 0)
{
lean_ctor_set_tag(v___x_5042_, 0);
lean_ctor_set(v___x_5042_, 0, v_e_5031_);
v___x_5046_ = v___x_5042_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_e_5031_);
v___x_5046_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; 
v___x_5047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5046_);
return v___x_5047_;
}
}
else
{
lean_object* v___x_5049_; 
lean_inc(v_us_5036_);
lean_dec_ref_known(v_e_5031_, 2);
v___x_5049_ = l_Lean_Core_instantiateValueLevelParams(v_val_5040_, v_us_5036_, v___x_5037_, v___y_5032_, v___y_5033_);
lean_dec(v_val_5040_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5060_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v_a_5050_);
v___x_5055_ = v___x_5042_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5057_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5055_);
v___x_5057_ = v___x_5052_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_del_object(v___x_5042_);
v_a_5061_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5049_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5049_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
}
else
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
lean_dec(v___x_5039_);
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v_e_5031_);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
return v___x_5071_;
}
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec_ref(v___x_5029_);
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v_e_5031_);
v___x_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
return v___x_5073_;
}
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; 
lean_dec_ref(v_e_5031_);
lean_dec_ref(v___x_5029_);
lean_dec_ref(v_env_5028_);
v___x_5074_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5074_);
return v___x_5075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_5076_, lean_object* v___x_5077_, lean_object* v___x_5078_, lean_object* v_e_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
uint8_t v___x_1999__boxed_5083_; lean_object* v_res_5084_; 
v___x_1999__boxed_5083_ = lean_unbox(v___x_5078_);
v_res_5084_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_5076_, v___x_5077_, v___x_1999__boxed_5083_, v_e_5079_, v___y_5080_, v___y_5081_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_5085_, lean_object* v_e_5086_, lean_object* v___f_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v___x_5091_; lean_object* v_env_5092_; uint8_t v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___f_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5091_ = lean_st_ref_get(v___y_5089_);
v_env_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc_ref(v_env_5092_);
lean_dec(v___x_5091_);
v___x_5093_ = 0;
v___x_5094_ = l_Lean_Environment_setExporting(v_biggerEnv_5085_, v___x_5093_);
v___x_5095_ = lean_box(v___x_5093_);
lean_inc_ref(v___x_5094_);
v___f_5096_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5096_, 0, v_env_5092_);
lean_closure_set(v___f_5096_, 1, v___x_5094_);
lean_closure_set(v___f_5096_, 2, v___x_5095_);
v___x_5097_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_5094_, v___y_5089_);
lean_dec_ref(v___x_5097_);
v___x_5098_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5086_, v___f_5096_, v___f_5087_, v___y_5088_, v___y_5089_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5099_, lean_object* v_e_5100_, lean_object* v___f_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5099_, v_e_5100_, v___f_5101_, v___y_5102_, v___y_5103_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5106_, lean_object* v_x_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v___x_5111_; lean_object* v_env_5112_; lean_object* v_a_5114_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5111_ = lean_st_ref_get(v___y_5109_);
v_env_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc_ref(v_env_5112_);
lean_dec(v___x_5111_);
v___x_5124_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5106_, v___y_5109_);
lean_dec_ref(v___x_5124_);
lean_inc(v___y_5109_);
lean_inc_ref(v___y_5108_);
v___x_5125_ = lean_apply_3(v_x_5107_, v___y_5108_, v___y_5109_, lean_box(0));
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
v___x_5127_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5112_, v___y_5109_);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5134_ == 0)
{
lean_object* v_unused_5135_; 
v_unused_5135_ = lean_ctor_get(v___x_5127_, 0);
lean_dec(v_unused_5135_);
v___x_5129_ = v___x_5127_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_dec(v___x_5127_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 0, v_a_5126_);
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5126_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
else
{
lean_object* v_a_5136_; 
v_a_5136_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5125_, 1);
v_a_5114_ = v_a_5136_;
goto v___jp_5113_;
}
v___jp_5113_:
{
lean_object* v___x_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
v___x_5115_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5112_, v___y_5109_);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; 
v_unused_5123_ = lean_ctor_get(v___x_5115_, 0);
lean_dec(v_unused_5123_);
v___x_5117_ = v___x_5115_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v___x_5115_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 1);
lean_ctor_set(v___x_5117_, 0, v_a_5114_);
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5114_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5137_, lean_object* v_x_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5137_, v_x_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5143_, lean_object* v_e_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v___f_5148_; lean_object* v___f_5149_; lean_object* v___x_5150_; lean_object* v_env_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___f_5148_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5149_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5149_, 0, v_biggerEnv_5143_);
lean_closure_set(v___f_5149_, 1, v_e_5144_);
lean_closure_set(v___f_5149_, 2, v___f_5148_);
v___x_5150_ = lean_st_ref_get(v_a_5146_);
v_env_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc_ref(v_env_5151_);
lean_dec(v___x_5150_);
v___x_5152_ = l_Lean_Environment_unlockAsync(v_env_5151_);
v___x_5153_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5152_, v___f_5149_, v_a_5145_, v_a_5146_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5154_, lean_object* v_e_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5154_, v_e_5155_, v_a_5156_, v_a_5157_);
lean_dec(v_a_5157_);
lean_dec_ref(v_a_5156_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5160_, lean_object* v_env_5161_, lean_object* v_x_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5161_, v_x_5162_, v___y_5163_, v___y_5164_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5167_, lean_object* v_env_5168_, lean_object* v_x_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5167_, v_env_5168_, v_x_5169_, v___y_5170_, v___y_5171_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
return v_res_5173_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5174_, lean_object* v_axs_5175_, lean_object* v_numSectionVars_5176_, lean_object* v_as_5177_, size_t v_i_5178_, size_t v_stop_5179_){
_start:
{
uint8_t v___x_5184_; 
v___x_5184_ = lean_usize_dec_eq(v_i_5178_, v_stop_5179_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5186_; uint8_t v___x_5187_; 
v___x_5185_ = lean_array_uget_borrowed(v_as_5177_, v_i_5178_);
v___x_5186_ = l_Lean_Expr_constName_x21(v_af_5174_);
v___x_5187_ = lean_name_eq(v___x_5186_, v___x_5185_);
lean_dec(v___x_5186_);
if (v___x_5187_ == 0)
{
goto v___jp_5180_;
}
else
{
lean_object* v___x_5188_; uint8_t v___x_5189_; 
v___x_5188_ = lean_array_get_size(v_axs_5175_);
v___x_5189_ = lean_nat_dec_le(v___x_5188_, v_numSectionVars_5176_);
if (v___x_5189_ == 0)
{
goto v___jp_5180_;
}
else
{
return v___x_5189_;
}
}
}
else
{
uint8_t v___x_5190_; 
v___x_5190_ = 0;
return v___x_5190_;
}
v___jp_5180_:
{
size_t v___x_5181_; size_t v___x_5182_; 
v___x_5181_ = ((size_t)1ULL);
v___x_5182_ = lean_usize_add(v_i_5178_, v___x_5181_);
v_i_5178_ = v___x_5182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5191_, lean_object* v_axs_5192_, lean_object* v_numSectionVars_5193_, lean_object* v_as_5194_, lean_object* v_i_5195_, lean_object* v_stop_5196_){
_start:
{
size_t v_i_boxed_5197_; size_t v_stop_boxed_5198_; uint8_t v_res_5199_; lean_object* v_r_5200_; 
v_i_boxed_5197_ = lean_unbox_usize(v_i_5195_);
lean_dec(v_i_5195_);
v_stop_boxed_5198_ = lean_unbox_usize(v_stop_5196_);
lean_dec(v_stop_5196_);
v_res_5199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5191_, v_axs_5192_, v_numSectionVars_5193_, v_as_5194_, v_i_boxed_5197_, v_stop_boxed_5198_);
lean_dec_ref(v_as_5194_);
lean_dec(v_numSectionVars_5193_);
lean_dec_ref(v_axs_5192_);
lean_dec_ref(v_af_5191_);
v_r_5200_ = lean_box(v_res_5199_);
return v_r_5200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5201_, lean_object* v_numSectionVars_5202_, lean_object* v_x_5203_, lean_object* v_x_5204_, lean_object* v_x_5205_){
_start:
{
if (lean_obj_tag(v_x_5203_) == 5)
{
lean_object* v_fn_5206_; lean_object* v_arg_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v_fn_5206_ = lean_ctor_get(v_x_5203_, 0);
lean_inc_ref(v_fn_5206_);
v_arg_5207_ = lean_ctor_get(v_x_5203_, 1);
lean_inc_ref(v_arg_5207_);
lean_dec_ref_known(v_x_5203_, 2);
v___x_5208_ = lean_array_set(v_x_5204_, v_x_5205_, v_arg_5207_);
v___x_5209_ = lean_unsigned_to_nat(1u);
v___x_5210_ = lean_nat_sub(v_x_5205_, v___x_5209_);
lean_dec(v_x_5205_);
v_x_5203_ = v_fn_5206_;
v_x_5204_ = v___x_5208_;
v_x_5205_ = v___x_5210_;
goto _start;
}
else
{
uint8_t v___x_5212_; 
lean_dec(v_x_5205_);
v___x_5212_ = l_Lean_Expr_isConst(v_x_5203_);
if (v___x_5212_ == 0)
{
lean_dec_ref(v_x_5204_);
lean_dec_ref(v_x_5203_);
return v___x_5212_;
}
else
{
lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_array_get_size(v_fnNames_5201_);
v___x_5215_ = lean_nat_dec_lt(v___x_5213_, v___x_5214_);
if (v___x_5215_ == 0)
{
lean_dec_ref(v_x_5204_);
lean_dec_ref(v_x_5203_);
return v___x_5215_;
}
else
{
if (v___x_5215_ == 0)
{
lean_dec_ref(v_x_5204_);
lean_dec_ref(v_x_5203_);
return v___x_5215_;
}
else
{
size_t v___x_5216_; size_t v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = ((size_t)0ULL);
v___x_5217_ = lean_usize_of_nat(v___x_5214_);
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5203_, v_x_5204_, v_numSectionVars_5202_, v_fnNames_5201_, v___x_5216_, v___x_5217_);
lean_dec_ref(v_x_5204_);
lean_dec_ref(v_x_5203_);
return v___x_5218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5219_, lean_object* v_numSectionVars_5220_, lean_object* v_x_5221_, lean_object* v_x_5222_, lean_object* v_x_5223_){
_start:
{
uint8_t v_res_5224_; lean_object* v_r_5225_; 
v_res_5224_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5219_, v_numSectionVars_5220_, v_x_5221_, v_x_5222_, v_x_5223_);
lean_dec(v_numSectionVars_5220_);
lean_dec_ref(v_fnNames_5219_);
v_r_5225_ = lean_box(v_res_5224_);
return v_r_5225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5226_, lean_object* v_fnNames_5227_, lean_object* v_x_5228_, lean_object* v_x_5229_, lean_object* v_x_5230_){
_start:
{
if (lean_obj_tag(v_x_5228_) == 5)
{
lean_object* v_fn_5231_; lean_object* v_arg_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; uint8_t v___x_5236_; 
v_fn_5231_ = lean_ctor_get(v_x_5228_, 0);
lean_inc_ref(v_fn_5231_);
v_arg_5232_ = lean_ctor_get(v_x_5228_, 1);
lean_inc_ref(v_arg_5232_);
lean_dec_ref_known(v_x_5228_, 2);
v___x_5233_ = lean_array_set(v_x_5229_, v_x_5230_, v_arg_5232_);
v___x_5234_ = lean_unsigned_to_nat(1u);
v___x_5235_ = lean_nat_sub(v_x_5230_, v___x_5234_);
v___x_5236_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5227_, v_numSectionVars_5226_, v_fn_5231_, v___x_5233_, v___x_5235_);
return v___x_5236_;
}
else
{
uint8_t v___x_5237_; 
v___x_5237_ = l_Lean_Expr_isConst(v_x_5228_);
if (v___x_5237_ == 0)
{
lean_dec_ref(v_x_5229_);
lean_dec_ref(v_x_5228_);
return v___x_5237_;
}
else
{
lean_object* v___x_5238_; lean_object* v___x_5239_; uint8_t v___x_5240_; 
v___x_5238_ = lean_unsigned_to_nat(0u);
v___x_5239_ = lean_array_get_size(v_fnNames_5227_);
v___x_5240_ = lean_nat_dec_lt(v___x_5238_, v___x_5239_);
if (v___x_5240_ == 0)
{
lean_dec_ref(v_x_5229_);
lean_dec_ref(v_x_5228_);
return v___x_5240_;
}
else
{
if (v___x_5240_ == 0)
{
lean_dec_ref(v_x_5229_);
lean_dec_ref(v_x_5228_);
return v___x_5240_;
}
else
{
size_t v___x_5241_; size_t v___x_5242_; uint8_t v___x_5243_; 
v___x_5241_ = ((size_t)0ULL);
v___x_5242_ = lean_usize_of_nat(v___x_5239_);
v___x_5243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5228_, v_x_5229_, v_numSectionVars_5226_, v_fnNames_5227_, v___x_5241_, v___x_5242_);
lean_dec_ref(v_x_5229_);
lean_dec_ref(v_x_5228_);
return v___x_5243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5244_, lean_object* v_fnNames_5245_, lean_object* v_x_5246_, lean_object* v_x_5247_, lean_object* v_x_5248_){
_start:
{
uint8_t v_res_5249_; lean_object* v_r_5250_; 
v_res_5249_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5244_, v_fnNames_5245_, v_x_5246_, v_x_5247_, v_x_5248_);
lean_dec(v_x_5248_);
lean_dec_ref(v_fnNames_5245_);
lean_dec(v_numSectionVars_5244_);
v_r_5250_ = lean_box(v_res_5249_);
return v_r_5250_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5251_, lean_object* v_numSectionVars_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v_dummy_5254_; lean_object* v_nargs_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; uint8_t v___x_5259_; 
v_dummy_5254_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5255_ = l_Lean_Expr_getAppNumArgs(v_a_5253_);
lean_inc(v_nargs_5255_);
v___x_5256_ = lean_mk_array(v_nargs_5255_, v_dummy_5254_);
v___x_5257_ = lean_unsigned_to_nat(1u);
v___x_5258_ = lean_nat_sub(v_nargs_5255_, v___x_5257_);
lean_dec(v_nargs_5255_);
v___x_5259_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5252_, v_fnNames_5251_, v_a_5253_, v___x_5256_, v___x_5258_);
lean_dec(v___x_5258_);
return v___x_5259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5260_, lean_object* v_numSectionVars_5261_, lean_object* v_a_5262_){
_start:
{
uint8_t v_res_5263_; lean_object* v_r_5264_; 
v_res_5263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5260_, v_numSectionVars_5261_, v_a_5262_);
lean_dec(v_numSectionVars_5261_);
lean_dec_ref(v_fnNames_5260_);
v_r_5264_ = lean_box(v_res_5263_);
return v_r_5264_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5265_, lean_object* v_numSectionVars_5266_, lean_object* v_as_5267_, size_t v_i_5268_, size_t v_stop_5269_){
_start:
{
uint8_t v___x_5270_; 
v___x_5270_ = lean_usize_dec_eq(v_i_5268_, v_stop_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; uint8_t v___x_5272_; 
v___x_5271_ = lean_array_uget_borrowed(v_as_5267_, v_i_5268_);
lean_inc(v___x_5271_);
v___x_5272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5265_, v_numSectionVars_5266_, v___x_5271_);
if (v___x_5272_ == 0)
{
size_t v___x_5273_; size_t v___x_5274_; 
v___x_5273_ = ((size_t)1ULL);
v___x_5274_ = lean_usize_add(v_i_5268_, v___x_5273_);
v_i_5268_ = v___x_5274_;
goto _start;
}
else
{
return v___x_5272_;
}
}
else
{
uint8_t v___x_5276_; 
v___x_5276_ = 0;
return v___x_5276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5277_, lean_object* v_numSectionVars_5278_, lean_object* v_as_5279_, lean_object* v_i_5280_, lean_object* v_stop_5281_){
_start:
{
size_t v_i_boxed_5282_; size_t v_stop_boxed_5283_; uint8_t v_res_5284_; lean_object* v_r_5285_; 
v_i_boxed_5282_ = lean_unbox_usize(v_i_5280_);
lean_dec(v_i_5280_);
v_stop_boxed_5283_ = lean_unbox_usize(v_stop_5281_);
lean_dec(v_stop_5281_);
v_res_5284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5277_, v_numSectionVars_5278_, v_as_5279_, v_i_boxed_5282_, v_stop_boxed_5283_);
lean_dec_ref(v_as_5279_);
lean_dec(v_numSectionVars_5278_);
lean_dec_ref(v_fnNames_5277_);
v_r_5285_ = lean_box(v_res_5284_);
return v_r_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5286_, lean_object* v_numSectionVars_5287_, lean_object* v___x_5288_, lean_object* v_x_5289_, lean_object* v_x_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_){
_start:
{
if (lean_obj_tag(v_x_5289_) == 5)
{
lean_object* v_fn_5297_; lean_object* v_arg_5298_; lean_object* v___x_5299_; 
v_fn_5297_ = lean_ctor_get(v_x_5289_, 0);
lean_inc_ref(v_fn_5297_);
v_arg_5298_ = lean_ctor_get(v_x_5289_, 1);
lean_inc_ref(v_arg_5298_);
lean_dec_ref_known(v_x_5289_, 2);
v___x_5299_ = lean_array_push(v_x_5290_, v_arg_5298_);
v_x_5289_ = v_fn_5297_;
v_x_5290_ = v___x_5299_;
goto _start;
}
else
{
uint8_t v___x_5301_; 
v___x_5301_ = l_Lean_Expr_isConst(v_x_5289_);
if (v___x_5301_ == 0)
{
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
lean_dec_ref(v___x_5288_);
goto v___jp_5294_;
}
else
{
lean_object* v___x_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; 
v___x_5302_ = lean_unsigned_to_nat(0u);
v___x_5303_ = lean_array_get_size(v_x_5290_);
v___x_5304_ = lean_nat_dec_lt(v___x_5302_, v___x_5303_);
if (v___x_5304_ == 0)
{
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
lean_dec_ref(v___x_5288_);
goto v___jp_5294_;
}
else
{
if (v___x_5304_ == 0)
{
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
lean_dec_ref(v___x_5288_);
goto v___jp_5294_;
}
else
{
size_t v___x_5305_; size_t v___x_5306_; uint8_t v___x_5307_; 
v___x_5305_ = ((size_t)0ULL);
v___x_5306_ = lean_usize_of_nat(v___x_5303_);
v___x_5307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5286_, v_numSectionVars_5287_, v_x_5290_, v___x_5305_, v___x_5306_);
if (v___x_5307_ == 0)
{
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
lean_dec_ref(v___x_5288_);
goto v___jp_5294_;
}
else
{
lean_object* v___x_5308_; uint8_t v___x_5309_; lean_object* v___x_5310_; 
v___x_5308_ = l_Lean_Expr_constName_x21(v_x_5289_);
v___x_5309_ = 0;
v___x_5310_ = l_Lean_Environment_find_x3f(v___x_5288_, v___x_5308_, v___x_5309_);
if (lean_obj_tag(v___x_5310_) == 1)
{
lean_object* v_val_5311_; 
v_val_5311_ = lean_ctor_get(v___x_5310_, 0);
lean_inc(v_val_5311_);
lean_dec_ref_known(v___x_5310_, 1);
if (lean_obj_tag(v_val_5311_) == 2)
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5337_; 
v___x_5312_ = l_Lean_Expr_constLevels_x21(v_x_5289_);
lean_dec_ref(v_x_5289_);
v___x_5313_ = l_Lean_Core_instantiateValueLevelParams(v_val_5311_, v___x_5312_, v___x_5304_, v___y_5291_, v___y_5292_);
v_isSharedCheck_5337_ = !lean_is_exclusive(v_val_5311_);
if (v_isSharedCheck_5337_ == 0)
{
lean_object* v_unused_5338_; 
v_unused_5338_ = lean_ctor_get(v_val_5311_, 0);
lean_dec(v_unused_5338_);
v___x_5315_ = v_val_5311_;
v_isShared_5316_ = v_isSharedCheck_5337_;
goto v_resetjp_5314_;
}
else
{
lean_dec(v_val_5311_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5337_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5328_; 
v_a_5317_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5319_ = v___x_5313_;
v_isShared_5320_ = v_isSharedCheck_5328_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5313_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5328_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = l_Lean_Expr_betaRev(v_a_5317_, v_x_5290_, v___x_5309_, v___x_5309_);
lean_dec_ref(v_x_5290_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set_tag(v___x_5315_, 1);
lean_ctor_set(v___x_5315_, 0, v___x_5321_);
v___x_5323_ = v___x_5315_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5321_);
v___x_5323_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5325_; 
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5323_);
v___x_5325_ = v___x_5319_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5323_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_del_object(v___x_5315_);
lean_dec_ref(v_x_5290_);
v_a_5329_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5313_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5313_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
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
else
{
lean_dec(v_val_5311_);
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
goto v___jp_5294_;
}
}
else
{
lean_dec(v___x_5310_);
lean_dec_ref(v_x_5290_);
lean_dec_ref(v_x_5289_);
goto v___jp_5294_;
}
}
}
}
}
}
v___jp_5294_:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5295_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
return v___x_5296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5339_, lean_object* v_numSectionVars_5340_, lean_object* v___x_5341_, lean_object* v_x_5342_, lean_object* v_x_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5339_, v_numSectionVars_5340_, v___x_5341_, v_x_5342_, v_x_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v_numSectionVars_5340_);
lean_dec_ref(v_fnNames_5339_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5348_, lean_object* v_numSectionVars_5349_, lean_object* v_env_5350_, lean_object* v_e_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5355_ = l_Lean_Expr_getAppNumArgs(v_e_5351_);
v___x_5356_ = lean_mk_empty_array_with_capacity(v___x_5355_);
lean_dec(v___x_5355_);
v___x_5357_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5348_, v_numSectionVars_5349_, v_env_5350_, v_e_5351_, v___x_5356_, v___y_5352_, v___y_5353_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5358_, lean_object* v_numSectionVars_5359_, lean_object* v_env_5360_, lean_object* v_e_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5358_, v_numSectionVars_5359_, v_env_5360_, v_e_5361_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v_numSectionVars_5359_);
lean_dec_ref(v_fnNames_5358_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5366_, lean_object* v_numSectionVars_5367_, lean_object* v_e_5368_, lean_object* v___f_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v___x_5373_; lean_object* v_env_5374_; lean_object* v___f_5375_; lean_object* v___x_5376_; 
v___x_5373_ = lean_st_ref_get(v___y_5371_);
v_env_5374_ = lean_ctor_get(v___x_5373_, 0);
lean_inc_ref(v_env_5374_);
lean_dec(v___x_5373_);
v___f_5375_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5375_, 0, v_fnNames_5366_);
lean_closure_set(v___f_5375_, 1, v_numSectionVars_5367_);
lean_closure_set(v___f_5375_, 2, v_env_5374_);
v___x_5376_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5368_, v___f_5375_, v___f_5369_, v___y_5370_, v___y_5371_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5377_, lean_object* v_numSectionVars_5378_, lean_object* v_e_5379_, lean_object* v___f_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5377_, v_numSectionVars_5378_, v_e_5379_, v___f_5380_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5385_, uint8_t v_isExporting_5386_, lean_object* v___x_5387_, lean_object* v_a_x3f_5388_){
_start:
{
lean_object* v___x_5390_; lean_object* v_env_5391_; lean_object* v_nextMacroScope_5392_; lean_object* v_ngen_5393_; lean_object* v_auxDeclNGen_5394_; lean_object* v_traceState_5395_; lean_object* v_recordedDeps_5396_; lean_object* v_messages_5397_; lean_object* v_infoState_5398_; lean_object* v_snapshotTasks_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5410_; 
v___x_5390_ = lean_st_ref_take(v___y_5385_);
v_env_5391_ = lean_ctor_get(v___x_5390_, 0);
v_nextMacroScope_5392_ = lean_ctor_get(v___x_5390_, 1);
v_ngen_5393_ = lean_ctor_get(v___x_5390_, 2);
v_auxDeclNGen_5394_ = lean_ctor_get(v___x_5390_, 3);
v_traceState_5395_ = lean_ctor_get(v___x_5390_, 4);
v_recordedDeps_5396_ = lean_ctor_get(v___x_5390_, 6);
v_messages_5397_ = lean_ctor_get(v___x_5390_, 7);
v_infoState_5398_ = lean_ctor_get(v___x_5390_, 8);
v_snapshotTasks_5399_ = lean_ctor_get(v___x_5390_, 9);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; 
v_unused_5411_ = lean_ctor_get(v___x_5390_, 5);
lean_dec(v_unused_5411_);
v___x_5401_ = v___x_5390_;
v_isShared_5402_ = v_isSharedCheck_5410_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_snapshotTasks_5399_);
lean_inc(v_infoState_5398_);
lean_inc(v_messages_5397_);
lean_inc(v_recordedDeps_5396_);
lean_inc(v_traceState_5395_);
lean_inc(v_auxDeclNGen_5394_);
lean_inc(v_ngen_5393_);
lean_inc(v_nextMacroScope_5392_);
lean_inc(v_env_5391_);
lean_dec(v___x_5390_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5410_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5403_ = lean_box(0);
v___x_5404_ = l_Lean_Environment_setExporting(v_env_5391_, v_isExporting_5386_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 5, v___x_5387_);
lean_ctor_set(v___x_5401_, 0, v___x_5404_);
v___x_5406_ = v___x_5401_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v___x_5404_);
lean_ctor_set(v_reuseFailAlloc_5409_, 1, v_nextMacroScope_5392_);
lean_ctor_set(v_reuseFailAlloc_5409_, 2, v_ngen_5393_);
lean_ctor_set(v_reuseFailAlloc_5409_, 3, v_auxDeclNGen_5394_);
lean_ctor_set(v_reuseFailAlloc_5409_, 4, v_traceState_5395_);
lean_ctor_set(v_reuseFailAlloc_5409_, 5, v___x_5387_);
lean_ctor_set(v_reuseFailAlloc_5409_, 6, v_recordedDeps_5396_);
lean_ctor_set(v_reuseFailAlloc_5409_, 7, v_messages_5397_);
lean_ctor_set(v_reuseFailAlloc_5409_, 8, v_infoState_5398_);
lean_ctor_set(v_reuseFailAlloc_5409_, 9, v_snapshotTasks_5399_);
v___x_5406_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = lean_st_ref_put(v___y_5385_, v___x_5406_);
v___x_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5403_);
return v___x_5408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5412_, lean_object* v_isExporting_5413_, lean_object* v___x_5414_, lean_object* v_a_x3f_5415_, lean_object* v___y_5416_){
_start:
{
uint8_t v_isExporting_boxed_5417_; lean_object* v_res_5418_; 
v_isExporting_boxed_5417_ = lean_unbox(v_isExporting_5413_);
v_res_5418_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5412_, v_isExporting_boxed_5417_, v___x_5414_, v_a_x3f_5415_);
lean_dec(v_a_x3f_5415_);
lean_dec(v___y_5412_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5419_, uint8_t v_isExporting_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v___x_5424_; lean_object* v_env_5425_; lean_object* v___x_5426_; uint8_t v_isModule_5427_; 
v___x_5424_ = lean_st_ref_get(v___y_5422_);
v_env_5425_ = lean_ctor_get(v___x_5424_, 0);
lean_inc_ref(v_env_5425_);
lean_dec(v___x_5424_);
v___x_5426_ = l_Lean_Environment_header(v_env_5425_);
v_isModule_5427_ = lean_ctor_get_uint8(v___x_5426_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5426_);
if (v_isModule_5427_ == 0)
{
lean_object* v___x_5428_; 
lean_dec_ref(v_env_5425_);
lean_inc(v___y_5422_);
lean_inc_ref(v___y_5421_);
v___x_5428_ = lean_apply_3(v_x_5419_, v___y_5421_, v___y_5422_, lean_box(0));
return v___x_5428_;
}
else
{
uint8_t v_isExporting_5429_; 
v_isExporting_5429_ = lean_ctor_get_uint8(v_env_5425_, sizeof(void*)*13);
lean_dec_ref(v_env_5425_);
if (v_isExporting_5420_ == 0)
{
if (v_isExporting_5429_ == 0)
{
lean_object* v___x_5481_; 
lean_inc(v___y_5422_);
lean_inc_ref(v___y_5421_);
v___x_5481_ = lean_apply_3(v_x_5419_, v___y_5421_, v___y_5422_, lean_box(0));
return v___x_5481_;
}
else
{
goto v___jp_5430_;
}
}
else
{
if (v_isExporting_5429_ == 0)
{
goto v___jp_5430_;
}
else
{
lean_object* v___x_5482_; 
lean_inc(v___y_5422_);
lean_inc_ref(v___y_5421_);
v___x_5482_ = lean_apply_3(v_x_5419_, v___y_5421_, v___y_5422_, lean_box(0));
return v___x_5482_;
}
}
v___jp_5430_:
{
lean_object* v___x_5431_; lean_object* v_env_5432_; lean_object* v_nextMacroScope_5433_; lean_object* v_ngen_5434_; lean_object* v_auxDeclNGen_5435_; lean_object* v_traceState_5436_; lean_object* v_recordedDeps_5437_; lean_object* v_messages_5438_; lean_object* v_infoState_5439_; lean_object* v_snapshotTasks_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5479_; 
v___x_5431_ = lean_st_ref_take(v___y_5422_);
v_env_5432_ = lean_ctor_get(v___x_5431_, 0);
v_nextMacroScope_5433_ = lean_ctor_get(v___x_5431_, 1);
v_ngen_5434_ = lean_ctor_get(v___x_5431_, 2);
v_auxDeclNGen_5435_ = lean_ctor_get(v___x_5431_, 3);
v_traceState_5436_ = lean_ctor_get(v___x_5431_, 4);
v_recordedDeps_5437_ = lean_ctor_get(v___x_5431_, 6);
v_messages_5438_ = lean_ctor_get(v___x_5431_, 7);
v_infoState_5439_ = lean_ctor_get(v___x_5431_, 8);
v_snapshotTasks_5440_ = lean_ctor_get(v___x_5431_, 9);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5479_ == 0)
{
lean_object* v_unused_5480_; 
v_unused_5480_ = lean_ctor_get(v___x_5431_, 5);
lean_dec(v_unused_5480_);
v___x_5442_ = v___x_5431_;
v_isShared_5443_ = v_isSharedCheck_5479_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_snapshotTasks_5440_);
lean_inc(v_infoState_5439_);
lean_inc(v_messages_5438_);
lean_inc(v_recordedDeps_5437_);
lean_inc(v_traceState_5436_);
lean_inc(v_auxDeclNGen_5435_);
lean_inc(v_ngen_5434_);
lean_inc(v_nextMacroScope_5433_);
lean_inc(v_env_5432_);
lean_dec(v___x_5431_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5479_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5447_; 
v___x_5444_ = l_Lean_Environment_setExporting(v_env_5432_, v_isExporting_5420_);
v___x_5445_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 5, v___x_5445_);
lean_ctor_set(v___x_5442_, 0, v___x_5444_);
v___x_5447_ = v___x_5442_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5444_);
lean_ctor_set(v_reuseFailAlloc_5478_, 1, v_nextMacroScope_5433_);
lean_ctor_set(v_reuseFailAlloc_5478_, 2, v_ngen_5434_);
lean_ctor_set(v_reuseFailAlloc_5478_, 3, v_auxDeclNGen_5435_);
lean_ctor_set(v_reuseFailAlloc_5478_, 4, v_traceState_5436_);
lean_ctor_set(v_reuseFailAlloc_5478_, 5, v___x_5445_);
lean_ctor_set(v_reuseFailAlloc_5478_, 6, v_recordedDeps_5437_);
lean_ctor_set(v_reuseFailAlloc_5478_, 7, v_messages_5438_);
lean_ctor_set(v_reuseFailAlloc_5478_, 8, v_infoState_5439_);
lean_ctor_set(v_reuseFailAlloc_5478_, 9, v_snapshotTasks_5440_);
v___x_5447_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
lean_object* v___x_5448_; lean_object* v_r_5449_; 
v___x_5448_ = lean_st_ref_put(v___y_5422_, v___x_5447_);
lean_inc(v___y_5422_);
lean_inc_ref(v___y_5421_);
v_r_5449_ = lean_apply_3(v_x_5419_, v___y_5421_, v___y_5422_, lean_box(0));
if (lean_obj_tag(v_r_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5466_; 
v_a_5450_ = lean_ctor_get(v_r_5449_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v_r_5449_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5452_ = v_r_5449_;
v_isShared_5453_ = v_isSharedCheck_5466_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v_r_5449_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5466_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
lean_inc(v_a_5450_);
if (v_isShared_5453_ == 0)
{
lean_ctor_set_tag(v___x_5452_, 1);
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
v___x_5456_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5422_, v_isExporting_5429_, v___x_5445_, v___x_5455_);
lean_dec_ref(v___x_5455_);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5463_ == 0)
{
lean_object* v_unused_5464_; 
v_unused_5464_ = lean_ctor_get(v___x_5456_, 0);
lean_dec(v_unused_5464_);
v___x_5458_ = v___x_5456_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_dec(v___x_5456_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 0, v_a_5450_);
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5450_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
}
else
{
lean_object* v_a_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
v_a_5467_ = lean_ctor_get(v_r_5449_, 0);
lean_inc(v_a_5467_);
lean_dec_ref_known(v_r_5449_, 1);
v___x_5468_ = lean_box(0);
v___x_5469_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5422_, v_isExporting_5429_, v___x_5445_, v___x_5468_);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5476_ == 0)
{
lean_object* v_unused_5477_; 
v_unused_5477_ = lean_ctor_get(v___x_5469_, 0);
lean_dec(v_unused_5477_);
v___x_5471_ = v___x_5469_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_dec(v___x_5469_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set_tag(v___x_5471_, 1);
lean_ctor_set(v___x_5471_, 0, v_a_5467_);
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5467_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5483_, lean_object* v_isExporting_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
uint8_t v_isExporting_boxed_5488_; lean_object* v_res_5489_; 
v_isExporting_boxed_5488_ = lean_unbox(v_isExporting_5484_);
v_res_5489_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5483_, v_isExporting_boxed_5488_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5490_, uint8_t v_when_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
if (v_when_5491_ == 0)
{
lean_object* v___x_5495_; 
lean_inc(v___y_5493_);
lean_inc_ref(v___y_5492_);
v___x_5495_ = lean_apply_3(v_x_5490_, v___y_5492_, v___y_5493_, lean_box(0));
return v___x_5495_;
}
else
{
uint8_t v___x_5496_; lean_object* v___x_5497_; 
v___x_5496_ = 0;
v___x_5497_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5490_, v___x_5496_, v___y_5492_, v___y_5493_);
return v___x_5497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5498_, lean_object* v_when_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
uint8_t v_when_boxed_5503_; lean_object* v_res_5504_; 
v_when_boxed_5503_ = lean_unbox(v_when_5499_);
v_res_5504_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5498_, v_when_boxed_5503_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
return v_res_5504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5505_, lean_object* v_numSectionVars_5506_, lean_object* v_e_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_){
_start:
{
lean_object* v___f_5511_; lean_object* v___f_5512_; uint8_t v___x_5513_; lean_object* v___x_5514_; 
v___f_5511_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5512_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5512_, 0, v_fnNames_5505_);
lean_closure_set(v___f_5512_, 1, v_numSectionVars_5506_);
lean_closure_set(v___f_5512_, 2, v_e_5507_);
lean_closure_set(v___f_5512_, 3, v___f_5511_);
v___x_5513_ = 1;
v___x_5514_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5512_, v___x_5513_, v_a_5508_, v_a_5509_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5515_, lean_object* v_numSectionVars_5516_, lean_object* v_e_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_){
_start:
{
lean_object* v_res_5521_; 
v_res_5521_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5515_, v_numSectionVars_5516_, v_e_5517_, v_a_5518_, v_a_5519_);
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
return v_res_5521_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5522_, lean_object* v_x_5523_, uint8_t v_isExporting_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v___x_5528_; 
v___x_5528_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5523_, v_isExporting_5524_, v___y_5525_, v___y_5526_);
return v___x_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5529_, lean_object* v_x_5530_, lean_object* v_isExporting_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
uint8_t v_isExporting_boxed_5535_; lean_object* v_res_5536_; 
v_isExporting_boxed_5535_ = lean_unbox(v_isExporting_5531_);
v_res_5536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5529_, v_x_5530_, v_isExporting_boxed_5535_, v___y_5532_, v___y_5533_);
lean_dec(v___y_5533_);
lean_dec_ref(v___y_5532_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5537_, lean_object* v_x_5538_, uint8_t v_when_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v___x_5543_; 
v___x_5543_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5538_, v_when_5539_, v___y_5540_, v___y_5541_);
return v___x_5543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5544_, lean_object* v_x_5545_, lean_object* v_when_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
uint8_t v_when_boxed_5550_; lean_object* v_res_5551_; 
v_when_boxed_5550_ = lean_unbox(v_when_5546_);
v_res_5551_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5544_, v_x_5545_, v_when_boxed_5550_, v___y_5547_, v___y_5548_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
return v_res_5551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5556_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5556_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_){
_start:
{
lean_object* v_res_5562_; 
v_res_5562_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5558_, v___y_5559_, v___y_5560_);
lean_dec(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_x_5558_);
return v_res_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v___y_5568_; lean_object* v___x_5571_; 
v___x_5571_ = l_Lean_inaccessible_x3f(v_e_5563_);
if (lean_obj_tag(v___x_5571_) == 1)
{
lean_object* v_val_5572_; 
lean_dec_ref(v_e_5563_);
v_val_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_val_5572_);
lean_dec_ref_known(v___x_5571_, 1);
v___y_5568_ = v_val_5572_;
goto v___jp_5567_;
}
else
{
lean_dec(v___x_5571_);
v___y_5568_ = v_e_5563_;
goto v___jp_5567_;
}
v___jp_5567_:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5569_, 0, v___y_5568_);
v___x_5570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5569_);
return v___x_5570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
lean_object* v_res_5577_; 
v_res_5577_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5573_, v___y_5574_, v___y_5575_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
return v_res_5577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_){
_start:
{
lean_object* v___f_5584_; lean_object* v___f_5585_; lean_object* v___x_5586_; 
v___f_5584_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5585_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5586_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5580_, v___f_5584_, v___f_5585_, v_a_5581_, v_a_5582_);
return v___x_5586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_){
_start:
{
lean_object* v_res_5591_; 
v_res_5591_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5587_, v_a_5588_, v_a_5589_);
lean_dec(v_a_5589_);
lean_dec_ref(v_a_5588_);
return v_res_5591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v___y_5597_; lean_object* v___x_5600_; 
v___x_5600_ = l_Lean_patternWithRef_x3f(v_e_5592_);
if (lean_obj_tag(v___x_5600_) == 1)
{
lean_object* v_val_5601_; lean_object* v_snd_5602_; 
lean_dec_ref(v_e_5592_);
v_val_5601_ = lean_ctor_get(v___x_5600_, 0);
lean_inc(v_val_5601_);
lean_dec_ref_known(v___x_5600_, 1);
v_snd_5602_ = lean_ctor_get(v_val_5601_, 1);
lean_inc(v_snd_5602_);
lean_dec(v_val_5601_);
v___y_5597_ = v_snd_5602_;
goto v___jp_5596_;
}
else
{
lean_dec(v___x_5600_);
v___y_5597_ = v_e_5592_;
goto v___jp_5596_;
}
v___jp_5596_:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; 
v___x_5598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5598_, 0, v___y_5597_);
v___x_5599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
return v___x_5599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5603_, v___y_5604_, v___y_5605_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
return v_res_5607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_){
_start:
{
lean_object* v___f_5613_; lean_object* v___f_5614_; lean_object* v___x_5615_; 
v___f_5613_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5614_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5615_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5609_, v___f_5613_, v___f_5614_, v_a_5610_, v_a_5611_);
return v___x_5615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5616_, v_a_5617_, v_a_5618_);
lean_dec(v_a_5618_);
lean_dec_ref(v_a_5617_);
return v_res_5620_;
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
