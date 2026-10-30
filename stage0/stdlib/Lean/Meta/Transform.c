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
lean_object* v___y_1097_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; uint8_t v___y_1111_; uint8_t v___y_1112_; uint16_t v___y_1113_; lean_object* v_toCold_1118_; lean_object* v_currRecDepth_1119_; lean_object* v_ref_1120_; uint16_t v_optionFlags_1121_; uint8_t v_suppressElabErrors_1122_; uint8_t v_checkDeprecated_1123_; uint8_t v_isRecordingDeps_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_cancelTk_x3f_1126_; 
v_toCold_1118_ = lean_ctor_get(v___y_1093_, 0);
v_currRecDepth_1119_ = lean_ctor_get(v___y_1093_, 1);
v_ref_1120_ = lean_ctor_get(v___y_1093_, 2);
v_optionFlags_1121_ = lean_ctor_get_uint16(v___y_1093_, sizeof(void*)*3);
v_suppressElabErrors_1122_ = lean_ctor_get_uint8(v___y_1093_, sizeof(void*)*3 + 2);
v_checkDeprecated_1123_ = lean_ctor_get_uint8(v___y_1093_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1124_ = lean_ctor_get_uint8(v___y_1093_, sizeof(void*)*3 + 4);
v_maxRecDepth_1125_ = lean_ctor_get(v_toCold_1118_, 3);
v_cancelTk_x3f_1126_ = lean_ctor_get(v_toCold_1118_, 10);
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
lean_dec_ref(v_x_1091_);
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
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_add(v___y_1110_, v___x_1114_);
lean_inc_ref(v___y_1109_);
v___x_1116_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1116_, 0, v___y_1109_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set(v___x_1116_, 2, v___y_1108_);
lean_ctor_set_uint16(v___x_1116_, sizeof(void*)*3, v___y_1113_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 2, v___y_1112_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 3, v___y_1111_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 4, v___y_1107_);
lean_inc(v___y_1094_);
lean_inc(v___y_1092_);
v___x_1117_ = lean_apply_4(v_x_1091_, v___y_1092_, v___x_1116_, v___y_1094_, lean_box(0));
v___y_1097_ = v___x_1117_;
goto v___jp_1096_;
}
v___jp_1127_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v_maxRecDepth_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_nat_dec_eq(v_currRecDepth_1119_, v_maxRecDepth_1125_);
if (v___x_1130_ == 0)
{
lean_inc(v_ref_1120_);
v___y_1107_ = v_isRecordingDeps_1124_;
v___y_1108_ = v_ref_1120_;
v___y_1109_ = v_toCold_1118_;
v___y_1110_ = v_currRecDepth_1119_;
v___y_1111_ = v_checkDeprecated_1123_;
v___y_1112_ = v_suppressElabErrors_1122_;
v___y_1113_ = v_optionFlags_1121_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1131_; 
lean_dec_ref(v_x_1091_);
lean_inc(v_ref_1120_);
v___x_1131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1120_);
v___y_1097_ = v___x_1131_;
goto v___jp_1096_;
}
}
else
{
lean_inc(v_ref_1120_);
v___y_1107_ = v_isRecordingDeps_1124_;
v___y_1108_ = v_ref_1120_;
v___y_1109_ = v_toCold_1118_;
v___y_1110_ = v_currRecDepth_1119_;
v___y_1111_ = v_checkDeprecated_1123_;
v___y_1112_ = v_suppressElabErrors_1122_;
v___y_1113_ = v_optionFlags_1121_;
goto v___jp_1106_;
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
lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_3322__overap_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
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
v___x_3322__overap_1841_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1830_, v___x_1831_, v___x_1840_);
lean_inc(v_a_1832_);
v___x_1842_ = lean_apply_1(v___x_3322__overap_1841_, v_a_1832_);
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
uint8_t v___x_1869_; lean_object* v___x_3341__overap_1870_; lean_object* v___x_1871_; 
v___x_1869_ = 0;
v___x_3341__overap_1870_ = l_Lean_Meta_withLetDecl___redArg(v___x_1861_, v___x_1862_, v_declName_1863_, v_a_1864_, v_a_1868_, v___f_1865_, v_nondep_1866_, v___x_1869_);
lean_inc(v_a_1867_);
v___x_1871_ = lean_apply_1(v___x_3341__overap_1870_, v_a_1867_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v_declName_1874_, lean_object* v_a_1875_, lean_object* v___f_1876_, lean_object* v_nondep_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
uint8_t v_nondep_3520__boxed_1880_; lean_object* v_res_1881_; 
v_nondep_3520__boxed_1880_ = lean_unbox(v_nondep_1877_);
v_res_1881_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1872_, v___x_1873_, v_declName_1874_, v_a_1875_, v___f_1876_, v_nondep_3520__boxed_1880_, v_a_1878_, v_a_1879_);
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
uint8_t v___x_1936_; lean_object* v___x_3399__overap_1937_; lean_object* v___x_1938_; 
v___x_1936_ = 0;
v___x_3399__overap_1937_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1929_, v___x_1930_, v_binderName_1931_, v_binderInfo_1932_, v_a_1935_, v___f_1933_, v___x_1936_);
lean_inc(v_a_1934_);
v___x_1938_ = lean_apply_1(v___x_3399__overap_1937_, v_a_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_binderName_1941_, lean_object* v_binderInfo_1942_, lean_object* v___f_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v_binderInfo_3588__boxed_1946_; lean_object* v_res_1947_; 
v_binderInfo_3588__boxed_1946_ = lean_unbox(v_binderInfo_1942_);
v_res_1947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1939_, v___x_1940_, v_binderName_1941_, v_binderInfo_3588__boxed_1946_, v___f_1943_, v_a_1944_, v_a_1945_);
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
lean_object* v_paramInfo_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_3159__overap_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
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
v___x_3159__overap_2149_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2148_, v___x_2144_, v_args_2139_, lean_box(0));
lean_inc(v___y_2140_);
v___x_2150_ = lean_apply_1(v___x_3159__overap_2149_, v___y_2140_);
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
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_3172__overap_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
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
v___x_3172__overap_2201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2185_, v___x_2198_, v_sz_2199_, v___x_2200_, v_args_2184_);
v___x_2202_ = lean_apply_1(v___x_3172__overap_2201_, v___y_2190_);
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
uint8_t v_nondep_3730__boxed_2540_; uint8_t v_usedLetOnly_boxed_2541_; uint8_t v_skipConstInApp_boxed_2542_; uint8_t v_skipInstances_boxed_2543_; lean_object* v_res_2544_; 
v_nondep_3730__boxed_2540_ = lean_unbox(v_nondep_2524_);
v_usedLetOnly_boxed_2541_ = lean_unbox(v_usedLetOnly_2533_);
v_skipConstInApp_boxed_2542_ = lean_unbox(v_skipConstInApp_2534_);
v_skipInstances_boxed_2543_ = lean_unbox(v_skipInstances_2535_);
v_res_2544_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2520_, v___x_2521_, v_declName_2522_, v___f_2523_, v_nondep_3730__boxed_2540_, v_a_2525_, v_value_2526_, v_fvars_2527_, v_inst_2528_, v_inst_2529_, v_inst_2530_, v_pre_2531_, v_post_2532_, v_usedLetOnly_boxed_2541_, v_skipConstInApp_boxed_2542_, v_skipInstances_boxed_2543_, v_x_2536_, v_x_2537_, v_toBind_2538_, v_a_2539_);
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
lean_object* v_dummy_2699_; lean_object* v_nargs_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_3276__overap_2704_; lean_object* v___x_2705_; 
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
v___x_3276__overap_2704_ = l_Lean_Expr_withAppAux___redArg(v___f_2687_, v___y_2692_, v___x_2701_, v___x_2703_);
lean_inc(v___y_2686_);
v___x_2705_ = lean_apply_1(v___x_3276__overap_2704_, v___y_2686_);
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
lean_object* v___y_3739_; lean_object* v_toCold_3748_; lean_object* v_currRecDepth_3749_; lean_object* v_ref_3750_; uint16_t v_optionFlags_3751_; uint8_t v_suppressElabErrors_3752_; uint8_t v_checkDeprecated_3753_; uint8_t v_isRecordingDeps_3754_; lean_object* v_maxRecDepth_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_toCold_3748_ = lean_ctor_get(v___y_3735_, 0);
v_currRecDepth_3749_ = lean_ctor_get(v___y_3735_, 1);
v_ref_3750_ = lean_ctor_get(v___y_3735_, 2);
v_optionFlags_3751_ = lean_ctor_get_uint16(v___y_3735_, sizeof(void*)*3);
v_suppressElabErrors_3752_ = lean_ctor_get_uint8(v___y_3735_, sizeof(void*)*3 + 2);
v_checkDeprecated_3753_ = lean_ctor_get_uint8(v___y_3735_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3754_ = lean_ctor_get_uint8(v___y_3735_, sizeof(void*)*3 + 4);
v_maxRecDepth_3760_ = lean_ctor_get(v_toCold_3748_, 3);
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_nat_dec_eq(v_maxRecDepth_3760_, v___x_3761_);
if (v___x_3762_ == 0)
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_nat_dec_eq(v_currRecDepth_3749_, v_maxRecDepth_3760_);
if (v___x_3763_ == 0)
{
goto v___jp_3755_;
}
else
{
lean_object* v___x_3764_; 
lean_dec_ref(v_x_3731_);
lean_inc(v_ref_3750_);
v___x_3764_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3750_);
v___y_3739_ = v___x_3764_;
goto v___jp_3738_;
}
}
else
{
goto v___jp_3755_;
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
v___jp_3755_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_unsigned_to_nat(1u);
v___x_3757_ = lean_nat_add(v_currRecDepth_3749_, v___x_3756_);
lean_inc(v_ref_3750_);
lean_inc_ref(v_toCold_3748_);
v___x_3758_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3758_, 0, v_toCold_3748_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
lean_ctor_set(v___x_3758_, 2, v_ref_3750_);
lean_ctor_set_uint16(v___x_3758_, sizeof(void*)*3, v_optionFlags_3751_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3 + 2, v_suppressElabErrors_3752_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3 + 3, v_checkDeprecated_3753_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3 + 4, v_isRecordingDeps_3754_);
lean_inc(v___y_3736_);
lean_inc(v___y_3734_);
lean_inc_ref(v___y_3733_);
lean_inc(v___y_3732_);
v___x_3759_ = lean_apply_6(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___x_3758_, v___y_3736_, lean_box(0));
v___y_3739_ = v___x_3759_;
goto v___jp_3738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3773_, lean_object* v_pre_3774_, lean_object* v_post_3775_, lean_object* v_usedLetOnly_3776_, lean_object* v_skipConstInApp_3777_, lean_object* v_skipInstances_3778_, lean_object* v_body_3779_, lean_object* v_x_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
uint8_t v_usedLetOnly_boxed_3787_; uint8_t v_skipConstInApp_boxed_3788_; uint8_t v_skipInstances_boxed_3789_; lean_object* v_res_3790_; 
v_usedLetOnly_boxed_3787_ = lean_unbox(v_usedLetOnly_3776_);
v_skipConstInApp_boxed_3788_ = lean_unbox(v_skipConstInApp_3777_);
v_skipInstances_boxed_3789_ = lean_unbox(v_skipInstances_3778_);
v_res_3790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3773_, v_pre_3774_, v_post_3775_, v_usedLetOnly_boxed_3787_, v_skipConstInApp_boxed_3788_, v_skipInstances_boxed_3789_, v_body_3779_, v_x_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3791_, lean_object* v_pre_3792_, lean_object* v_post_3793_, uint8_t v_usedLetOnly_3794_, uint8_t v_skipConstInApp_3795_, uint8_t v_skipInstances_3796_, lean_object* v_body_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_array_push(v_fvars_3791_, v_x_3798_);
v___x_3806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3792_, v_post_3793_, v_usedLetOnly_3794_, v_skipConstInApp_3795_, v_skipInstances_3796_, v___x_3805_, v_body_3797_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3807_, lean_object* v_pre_3808_, lean_object* v_post_3809_, lean_object* v_usedLetOnly_3810_, lean_object* v_skipConstInApp_3811_, lean_object* v_skipInstances_3812_, lean_object* v_body_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
uint8_t v_usedLetOnly_boxed_3821_; uint8_t v_skipConstInApp_boxed_3822_; uint8_t v_skipInstances_boxed_3823_; lean_object* v_res_3824_; 
v_usedLetOnly_boxed_3821_ = lean_unbox(v_usedLetOnly_3810_);
v_skipConstInApp_boxed_3822_ = lean_unbox(v_skipConstInApp_3811_);
v_skipInstances_boxed_3823_ = lean_unbox(v_skipInstances_3812_);
v_res_3824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3807_, v_pre_3808_, v_post_3809_, v_usedLetOnly_boxed_3821_, v_skipConstInApp_boxed_3822_, v_skipInstances_boxed_3823_, v_body_3813_, v_x_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3825_, lean_object* v_post_3826_, uint8_t v_usedLetOnly_3827_, uint8_t v_skipConstInApp_3828_, uint8_t v_skipInstances_3829_, lean_object* v_e_3830_, lean_object* v_a_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___x_3837_; 
lean_inc_ref(v_post_3826_);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc_ref(v_e_3830_);
v___x_3837_ = lean_apply_6(v_post_3826_, v_e_3830_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, lean_box(0));
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3856_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3856_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3856_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
switch(lean_obj_tag(v_a_3838_))
{
case 0:
{
lean_object* v_e_3842_; lean_object* v___x_3844_; 
lean_dec_ref(v_e_3830_);
lean_dec_ref(v_post_3826_);
lean_dec_ref(v_pre_3825_);
v_e_3842_ = lean_ctor_get(v_a_3838_, 0);
lean_inc_ref(v_e_3842_);
lean_dec_ref_known(v_a_3838_, 1);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_e_3842_);
v___x_3844_ = v___x_3840_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_e_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
case 1:
{
lean_object* v_e_3846_; lean_object* v___x_3847_; 
lean_del_object(v___x_3840_);
lean_dec_ref(v_e_3830_);
v_e_3846_ = lean_ctor_get(v_a_3838_, 0);
lean_inc_ref(v_e_3846_);
lean_dec_ref_known(v_a_3838_, 1);
v___x_3847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3825_, v_post_3826_, v_usedLetOnly_3827_, v_skipConstInApp_3828_, v_skipInstances_3829_, v_e_3846_, v_a_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3847_;
}
default: 
{
lean_object* v_e_x3f_3848_; 
lean_dec_ref(v_post_3826_);
lean_dec_ref(v_pre_3825_);
v_e_x3f_3848_ = lean_ctor_get(v_a_3838_, 0);
lean_inc(v_e_x3f_3848_);
lean_dec_ref_known(v_a_3838_, 1);
if (lean_obj_tag(v_e_x3f_3848_) == 0)
{
lean_object* v___x_3850_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_e_3830_);
v___x_3850_ = v___x_3840_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_e_3830_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
else
{
lean_object* v_val_3852_; lean_object* v___x_3854_; 
lean_dec_ref(v_e_3830_);
v_val_3852_ = lean_ctor_get(v_e_x3f_3848_, 0);
lean_inc(v_val_3852_);
lean_dec_ref_known(v_e_x3f_3848_, 1);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_val_3852_);
v___x_3854_ = v___x_3840_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_val_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v_e_3830_);
lean_dec_ref(v_post_3826_);
lean_dec_ref(v_pre_3825_);
v_a_3857_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3837_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3837_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3865_, lean_object* v_post_3866_, uint8_t v_usedLetOnly_3867_, uint8_t v_skipConstInApp_3868_, uint8_t v_skipInstances_3869_, lean_object* v_fvars_3870_, lean_object* v_e_3871_, lean_object* v_a_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
if (lean_obj_tag(v_e_3871_) == 6)
{
lean_object* v_binderName_3878_; lean_object* v_binderType_3879_; lean_object* v_body_3880_; uint8_t v_binderInfo_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___f_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_binderName_3878_ = lean_ctor_get(v_e_3871_, 0);
lean_inc(v_binderName_3878_);
v_binderType_3879_ = lean_ctor_get(v_e_3871_, 1);
lean_inc_ref(v_binderType_3879_);
v_body_3880_ = lean_ctor_get(v_e_3871_, 2);
lean_inc_ref(v_body_3880_);
v_binderInfo_3881_ = lean_ctor_get_uint8(v_e_3871_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3871_, 3);
v___x_3882_ = lean_box(v_usedLetOnly_3867_);
v___x_3883_ = lean_box(v_skipConstInApp_3868_);
v___x_3884_ = lean_box(v_skipInstances_3869_);
lean_inc_ref(v_post_3866_);
lean_inc_ref(v_pre_3865_);
lean_inc_ref(v_fvars_3870_);
v___f_3885_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3885_, 0, v_fvars_3870_);
lean_closure_set(v___f_3885_, 1, v_pre_3865_);
lean_closure_set(v___f_3885_, 2, v_post_3866_);
lean_closure_set(v___f_3885_, 3, v___x_3882_);
lean_closure_set(v___f_3885_, 4, v___x_3883_);
lean_closure_set(v___f_3885_, 5, v___x_3884_);
lean_closure_set(v___f_3885_, 6, v_body_3880_);
v___x_3886_ = lean_expr_instantiate_rev(v_binderType_3879_, v_fvars_3870_);
lean_dec_ref(v_fvars_3870_);
lean_dec_ref(v_binderType_3879_);
v___x_3887_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3865_, v_post_3866_, v_usedLetOnly_3867_, v_skipConstInApp_3868_, v_skipInstances_3869_, v___x_3886_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; uint8_t v___x_3889_; lean_object* v___x_3890_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = 0;
v___x_3890_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3878_, v_binderInfo_3881_, v_a_3888_, v___f_3885_, v___x_3889_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3890_;
}
else
{
lean_dec_ref(v___f_3885_);
lean_dec(v_binderName_3878_);
return v___x_3887_;
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_expr_instantiate_rev(v_e_3871_, v_fvars_3870_);
lean_dec_ref(v_e_3871_);
lean_inc_ref(v_post_3866_);
lean_inc_ref(v_pre_3865_);
v___x_3892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3865_, v_post_3866_, v_usedLetOnly_3867_, v_skipConstInApp_3868_, v_skipInstances_3869_, v___x_3891_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; uint8_t v___x_3894_; uint8_t v___x_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = 0;
v___x_3895_ = 1;
v___x_3896_ = 1;
v___x_3897_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3870_, v_a_3893_, v___x_3894_, v_usedLetOnly_3867_, v___x_3894_, v___x_3895_, v___x_3896_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec_ref(v_fvars_3870_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3865_, v_post_3866_, v_usedLetOnly_3867_, v_skipConstInApp_3868_, v_skipInstances_3869_, v_a_3898_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3899_;
}
else
{
lean_dec_ref(v_post_3866_);
lean_dec_ref(v_pre_3865_);
return v___x_3897_;
}
}
else
{
lean_dec_ref(v_fvars_3870_);
lean_dec_ref(v_post_3866_);
lean_dec_ref(v_pre_3865_);
return v___x_3892_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3900_, lean_object* v_pre_3901_, lean_object* v_post_3902_, uint8_t v_usedLetOnly_3903_, uint8_t v_skipConstInApp_3904_, uint8_t v_skipInstances_3905_, lean_object* v_body_3906_, lean_object* v_x_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_array_push(v_fvars_3900_, v_x_3907_);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3901_, v_post_3902_, v_usedLetOnly_3903_, v_skipConstInApp_3904_, v_skipInstances_3905_, v___x_3914_, v_body_3906_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3916_, lean_object* v_pre_3917_, lean_object* v_post_3918_, lean_object* v_usedLetOnly_3919_, lean_object* v_skipConstInApp_3920_, lean_object* v_skipInstances_3921_, lean_object* v_body_3922_, lean_object* v_x_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v_usedLetOnly_boxed_3930_; uint8_t v_skipConstInApp_boxed_3931_; uint8_t v_skipInstances_boxed_3932_; lean_object* v_res_3933_; 
v_usedLetOnly_boxed_3930_ = lean_unbox(v_usedLetOnly_3919_);
v_skipConstInApp_boxed_3931_ = lean_unbox(v_skipConstInApp_3920_);
v_skipInstances_boxed_3932_ = lean_unbox(v_skipInstances_3921_);
v_res_3933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3916_, v_pre_3917_, v_post_3918_, v_usedLetOnly_boxed_3930_, v_skipConstInApp_boxed_3931_, v_skipInstances_boxed_3932_, v_body_3922_, v_x_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3934_, lean_object* v_post_3935_, uint8_t v_usedLetOnly_3936_, uint8_t v_skipConstInApp_3937_, uint8_t v_skipInstances_3938_, lean_object* v_fvars_3939_, lean_object* v_e_3940_, lean_object* v_a_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
if (lean_obj_tag(v_e_3940_) == 8)
{
lean_object* v_declName_3947_; lean_object* v_type_3948_; lean_object* v_value_3949_; lean_object* v_body_3950_; uint8_t v_nondep_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_declName_3947_ = lean_ctor_get(v_e_3940_, 0);
lean_inc(v_declName_3947_);
v_type_3948_ = lean_ctor_get(v_e_3940_, 1);
lean_inc_ref(v_type_3948_);
v_value_3949_ = lean_ctor_get(v_e_3940_, 2);
lean_inc_ref(v_value_3949_);
v_body_3950_ = lean_ctor_get(v_e_3940_, 3);
lean_inc_ref(v_body_3950_);
v_nondep_3951_ = lean_ctor_get_uint8(v_e_3940_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3940_, 4);
v___x_3952_ = lean_box(v_usedLetOnly_3936_);
v___x_3953_ = lean_box(v_skipConstInApp_3937_);
v___x_3954_ = lean_box(v_skipInstances_3938_);
lean_inc_ref_n(v_post_3935_, 2);
lean_inc_ref_n(v_pre_3934_, 2);
lean_inc_ref(v_fvars_3939_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3955_, 0, v_fvars_3939_);
lean_closure_set(v___f_3955_, 1, v_pre_3934_);
lean_closure_set(v___f_3955_, 2, v_post_3935_);
lean_closure_set(v___f_3955_, 3, v___x_3952_);
lean_closure_set(v___f_3955_, 4, v___x_3953_);
lean_closure_set(v___f_3955_, 5, v___x_3954_);
lean_closure_set(v___f_3955_, 6, v_body_3950_);
v___x_3956_ = lean_expr_instantiate_rev(v_type_3948_, v_fvars_3939_);
lean_dec_ref(v_type_3948_);
v___x_3957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3934_, v_post_3935_, v_usedLetOnly_3936_, v_skipConstInApp_3937_, v_skipInstances_3938_, v___x_3956_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_expr_instantiate_rev(v_value_3949_, v_fvars_3939_);
lean_dec_ref(v_fvars_3939_);
lean_dec_ref(v_value_3949_);
v___x_3960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3934_, v_post_3935_, v_usedLetOnly_3936_, v_skipConstInApp_3937_, v_skipInstances_3938_, v___x_3959_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; uint8_t v___x_3962_; lean_object* v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v___x_3962_ = 0;
v___x_3963_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3947_, v_a_3958_, v_a_3961_, v___f_3955_, v_nondep_3951_, v___x_3962_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3963_;
}
else
{
lean_dec(v_a_3958_);
lean_dec_ref(v___f_3955_);
lean_dec(v_declName_3947_);
return v___x_3960_;
}
}
else
{
lean_dec_ref(v___f_3955_);
lean_dec_ref(v_value_3949_);
lean_dec(v_declName_3947_);
lean_dec_ref(v_fvars_3939_);
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
return v___x_3957_;
}
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_expr_instantiate_rev(v_e_3940_, v_fvars_3939_);
lean_dec_ref(v_e_3940_);
lean_inc_ref(v_post_3935_);
lean_inc_ref(v_pre_3934_);
v___x_3965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3934_, v_post_3935_, v_usedLetOnly_3936_, v_skipConstInApp_3937_, v_skipInstances_3938_, v___x_3964_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; uint8_t v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = 0;
v___x_3968_ = 1;
v___x_3969_ = l_Lean_Meta_mkLetFVars(v_fvars_3939_, v_a_3966_, v_usedLetOnly_3936_, v___x_3967_, v___x_3968_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec_ref(v_fvars_3939_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v___x_3971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3934_, v_post_3935_, v_usedLetOnly_3936_, v_skipConstInApp_3937_, v_skipInstances_3938_, v_a_3970_, v_a_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3971_;
}
else
{
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
return v___x_3969_;
}
}
else
{
lean_dec_ref(v_fvars_3939_);
lean_dec_ref(v_post_3935_);
lean_dec_ref(v_pre_3934_);
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3972_, lean_object* v_post_3973_, uint8_t v_usedLetOnly_3974_, uint8_t v_skipConstInApp_3975_, uint8_t v_skipInstances_3976_, size_t v_sz_3977_, size_t v_i_3978_, lean_object* v_bs_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v___x_3986_; 
v___x_3986_ = lean_usize_dec_lt(v_i_3978_, v_sz_3977_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref(v_post_3973_);
lean_dec_ref(v_pre_3972_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_bs_3979_);
return v___x_3987_;
}
else
{
lean_object* v_v_3988_; lean_object* v___x_3989_; lean_object* v_bs_x27_3990_; lean_object* v___x_3991_; 
v_v_3988_ = lean_array_uget(v_bs_3979_, v_i_3978_);
v___x_3989_ = lean_unsigned_to_nat(0u);
v_bs_x27_3990_ = lean_array_uset(v_bs_3979_, v_i_3978_, v___x_3989_);
lean_inc_ref(v_post_3973_);
lean_inc_ref(v_pre_3972_);
v___x_3991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3972_, v_post_3973_, v_usedLetOnly_3974_, v_skipConstInApp_3975_, v_skipInstances_3976_, v_v_3988_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; size_t v___x_3993_; size_t v___x_3994_; lean_object* v___x_3995_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v___x_3993_ = ((size_t)1ULL);
v___x_3994_ = lean_usize_add(v_i_3978_, v___x_3993_);
v___x_3995_ = lean_array_uset(v_bs_x27_3990_, v_i_3978_, v_a_3992_);
v_i_3978_ = v___x_3994_;
v_bs_3979_ = v___x_3995_;
goto _start;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec_ref(v_bs_x27_3990_);
lean_dec_ref(v_post_3973_);
lean_dec_ref(v_pre_3972_);
v_a_3997_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3991_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3991_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4005_, lean_object* v_post_4006_, uint8_t v_usedLetOnly_4007_, uint8_t v_skipConstInApp_4008_, uint8_t v_skipInstances_4009_, lean_object* v___x_4010_, lean_object* v___y_4011_, lean_object* v_b_4012_, lean_object* v_a_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4005_, v_post_4006_, v_usedLetOnly_4007_, v_skipConstInApp_4008_, v_skipInstances_4009_, v___x_4010_, v___y_4011_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4029_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4024_ = lean_array_fset(v_b_4012_, v_a_4013_, v_a_4020_);
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4025_);
v___x_4027_ = v___x_4022_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec_ref(v_b_4012_);
v_a_4030_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4019_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4019_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4038_, lean_object* v_post_4039_, lean_object* v_usedLetOnly_4040_, lean_object* v_skipConstInApp_4041_, lean_object* v_skipInstances_4042_, lean_object* v___x_4043_, lean_object* v___y_4044_, lean_object* v_b_4045_, lean_object* v_a_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
uint8_t v_usedLetOnly_boxed_4052_; uint8_t v_skipConstInApp_boxed_4053_; uint8_t v_skipInstances_boxed_4054_; lean_object* v_res_4055_; 
v_usedLetOnly_boxed_4052_ = lean_unbox(v_usedLetOnly_4040_);
v_skipConstInApp_boxed_4053_ = lean_unbox(v_skipConstInApp_4041_);
v_skipInstances_boxed_4054_ = lean_unbox(v_skipInstances_4042_);
v_res_4055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4038_, v_post_4039_, v_usedLetOnly_boxed_4052_, v_skipConstInApp_boxed_4053_, v_skipInstances_boxed_4054_, v___x_4043_, v___y_4044_, v_b_4045_, v_a_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v_a_4046_);
lean_dec(v___y_4044_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4056_, lean_object* v___x_4057_, lean_object* v_pre_4058_, lean_object* v_post_4059_, uint8_t v_usedLetOnly_4060_, uint8_t v_skipConstInApp_4061_, uint8_t v_skipInstances_4062_, lean_object* v_a_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___y_4072_; uint8_t v___x_4095_; 
v___x_4095_ = lean_nat_dec_lt(v_a_4063_, v_upperBound_4056_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_post_4059_);
lean_dec_ref(v_pre_4058_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_b_4064_);
return v___x_4096_;
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4097_ = lean_array_fget_borrowed(v_b_4064_, v_a_4063_);
v___x_4098_ = lean_array_get_size(v___x_4057_);
v___x_4099_ = lean_nat_dec_lt(v_a_4063_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___f_4103_; 
lean_inc(v___x_4097_);
v___x_4100_ = lean_box(v_usedLetOnly_4060_);
v___x_4101_ = lean_box(v_skipConstInApp_4061_);
v___x_4102_ = lean_box(v_skipInstances_4062_);
lean_inc(v_a_4063_);
lean_inc(v___y_4065_);
lean_inc_ref(v_post_4059_);
lean_inc_ref(v_pre_4058_);
v___f_4103_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4103_, 0, v_pre_4058_);
lean_closure_set(v___f_4103_, 1, v_post_4059_);
lean_closure_set(v___f_4103_, 2, v___x_4100_);
lean_closure_set(v___f_4103_, 3, v___x_4101_);
lean_closure_set(v___f_4103_, 4, v___x_4102_);
lean_closure_set(v___f_4103_, 5, v___x_4097_);
lean_closure_set(v___f_4103_, 6, v___y_4065_);
lean_closure_set(v___f_4103_, 7, v_b_4064_);
lean_closure_set(v___f_4103_, 8, v_a_4063_);
v___y_4072_ = v___f_4103_;
goto v___jp_4071_;
}
else
{
lean_object* v___x_4104_; uint8_t v_isInstance_4105_; 
v___x_4104_ = lean_array_fget_borrowed(v___x_4057_, v_a_4063_);
v_isInstance_4105_ = lean_ctor_get_uint8(v___x_4104_, sizeof(void*)*1 + 4);
if (v_isInstance_4105_ == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___f_4109_; 
lean_inc(v___x_4097_);
v___x_4106_ = lean_box(v_usedLetOnly_4060_);
v___x_4107_ = lean_box(v_skipConstInApp_4061_);
v___x_4108_ = lean_box(v_skipInstances_4062_);
lean_inc(v_a_4063_);
lean_inc(v___y_4065_);
lean_inc_ref(v_post_4059_);
lean_inc_ref(v_pre_4058_);
v___f_4109_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4109_, 0, v_pre_4058_);
lean_closure_set(v___f_4109_, 1, v_post_4059_);
lean_closure_set(v___f_4109_, 2, v___x_4106_);
lean_closure_set(v___f_4109_, 3, v___x_4107_);
lean_closure_set(v___f_4109_, 4, v___x_4108_);
lean_closure_set(v___f_4109_, 5, v___x_4097_);
lean_closure_set(v___f_4109_, 6, v___y_4065_);
lean_closure_set(v___f_4109_, 7, v_b_4064_);
lean_closure_set(v___f_4109_, 8, v_a_4063_);
v___y_4072_ = v___f_4109_;
goto v___jp_4071_;
}
else
{
lean_object* v___x_4110_; lean_object* v___f_4111_; 
v___x_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_b_4064_);
v___f_4111_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4111_, 0, v___x_4110_);
v___y_4072_ = v___f_4111_;
goto v___jp_4071_;
}
}
}
v___jp_4071_:
{
lean_object* v___x_4073_; 
lean_inc(v___y_4069_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4067_);
lean_inc_ref(v___y_4066_);
v___x_4073_ = lean_apply_5(v___y_4072_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, lean_box(0));
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4086_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4086_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4086_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
if (lean_obj_tag(v_a_4074_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_post_4059_);
lean_dec_ref(v_pre_4058_);
v_a_4078_ = lean_ctor_get(v_a_4074_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v_a_4074_, 1);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v_a_4078_);
v___x_4080_ = v___x_4076_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_del_object(v___x_4076_);
v_a_4082_ = lean_ctor_get(v_a_4074_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v_a_4074_, 1);
v___x_4083_ = lean_unsigned_to_nat(1u);
v___x_4084_ = lean_nat_add(v_a_4063_, v___x_4083_);
lean_dec(v_a_4063_);
v_a_4063_ = v___x_4084_;
v_b_4064_ = v_a_4082_;
goto _start;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_post_4059_);
lean_dec_ref(v_pre_4058_);
v_a_4087_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4073_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4073_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4112_, lean_object* v_pre_4113_, lean_object* v_post_4114_, uint8_t v_usedLetOnly_4115_, uint8_t v_skipConstInApp_4116_, lean_object* v_x_4117_, lean_object* v_x_4118_, lean_object* v_x_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_f_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; 
if (lean_obj_tag(v_x_4117_) == 5)
{
lean_object* v_fn_4175_; lean_object* v_arg_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_fn_4175_ = lean_ctor_get(v_x_4117_, 0);
lean_inc_ref(v_fn_4175_);
v_arg_4176_ = lean_ctor_get(v_x_4117_, 1);
lean_inc_ref(v_arg_4176_);
lean_dec_ref_known(v_x_4117_, 2);
v___x_4177_ = lean_array_set(v_x_4118_, v_x_4119_, v_arg_4176_);
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_sub(v_x_4119_, v___x_4178_);
lean_dec(v_x_4119_);
v_x_4117_ = v_fn_4175_;
v_x_4118_ = v___x_4177_;
v_x_4119_ = v___x_4179_;
goto _start;
}
else
{
lean_dec(v_x_4119_);
if (v_skipConstInApp_4116_ == 0)
{
goto v___jp_4172_;
}
else
{
uint8_t v___x_4181_; 
v___x_4181_ = l_Lean_Expr_isConst(v_x_4117_);
if (v___x_4181_ == 0)
{
goto v___jp_4172_;
}
else
{
v_f_4127_ = v_x_4117_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
v___y_4130_ = v___y_4122_;
v___y_4131_ = v___y_4123_;
v___y_4132_ = v___y_4124_;
goto v___jp_4126_;
}
}
}
v___jp_4126_:
{
if (v_skipInstances_4112_ == 0)
{
size_t v_sz_4133_; size_t v___x_4134_; lean_object* v___x_4135_; 
v_sz_4133_ = lean_array_size(v_x_4118_);
v___x_4134_ = ((size_t)0ULL);
lean_inc_ref(v_post_4114_);
lean_inc_ref(v_pre_4113_);
v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4113_, v_post_4114_, v_usedLetOnly_4115_, v_skipConstInApp_4116_, v_skipInstances_4112_, v_sz_4133_, v___x_4134_, v_x_4118_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = l_Lean_mkAppN(v_f_4127_, v_a_4136_);
lean_dec(v_a_4136_);
v___x_4138_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4113_, v_post_4114_, v_usedLetOnly_4115_, v_skipConstInApp_4116_, v_skipInstances_4112_, v___x_4137_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4138_;
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec_ref(v_f_4127_);
lean_dec_ref(v_post_4114_);
lean_dec_ref(v_pre_4113_);
v_a_4139_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4135_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4135_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_array_get_size(v_x_4118_);
lean_inc_ref(v_f_4127_);
v___x_4148_ = l_Lean_Meta_getFunInfoNArgs(v_f_4127_, v___x_4147_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v_paramInfo_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v_paramInfo_4150_ = lean_ctor_get(v_a_4149_, 0);
lean_inc_ref(v_paramInfo_4150_);
lean_dec(v_a_4149_);
v___x_4151_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4114_);
lean_inc_ref(v_pre_4113_);
v___x_4152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4147_, v_paramInfo_4150_, v_pre_4113_, v_post_4114_, v_usedLetOnly_4115_, v_skipConstInApp_4116_, v_skipInstances_4112_, v___x_4151_, v_x_4118_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec_ref(v_paramInfo_4150_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4154_ = l_Lean_mkAppN(v_f_4127_, v_a_4153_);
lean_dec(v_a_4153_);
v___x_4155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4113_, v_post_4114_, v_usedLetOnly_4115_, v_skipConstInApp_4116_, v_skipInstances_4112_, v___x_4154_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4155_;
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v_f_4127_);
lean_dec_ref(v_post_4114_);
lean_dec_ref(v_pre_4113_);
v_a_4156_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4152_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4152_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_f_4127_);
lean_dec_ref(v_x_4118_);
lean_dec_ref(v_post_4114_);
lean_dec_ref(v_pre_4113_);
v_a_4164_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4148_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4148_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
v___jp_4172_:
{
lean_object* v___x_4173_; 
lean_inc_ref(v_post_4114_);
lean_inc_ref(v_pre_4113_);
v___x_4173_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4113_, v_post_4114_, v_usedLetOnly_4115_, v_skipConstInApp_4116_, v_skipInstances_4112_, v_x_4117_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v_f_4127_ = v_a_4174_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
v___y_4130_ = v___y_4122_;
v___y_4131_ = v___y_4123_;
v___y_4132_ = v___y_4124_;
goto v___jp_4126_;
}
else
{
lean_dec_ref(v_x_4118_);
lean_dec_ref(v_post_4114_);
lean_dec_ref(v_pre_4113_);
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4182_, lean_object* v_pre_4183_, lean_object* v_e_4184_, lean_object* v_post_4185_, uint8_t v_usedLetOnly_4186_, uint8_t v_skipConstInApp_4187_, uint8_t v_skipInstances_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_Core_checkSystem(v___x_4182_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v___x_4196_; 
lean_dec_ref_known(v___x_4195_, 1);
lean_inc_ref(v_pre_4183_);
lean_inc(v___y_4193_);
lean_inc_ref(v___y_4192_);
lean_inc(v___y_4191_);
lean_inc_ref(v___y_4190_);
lean_inc_ref(v_e_4184_);
v___x_4196_ = lean_apply_6(v_pre_4183_, v_e_4184_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, lean_box(0));
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4245_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4245_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4245_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___y_4202_; 
switch(lean_obj_tag(v_a_4197_))
{
case 0:
{
lean_object* v_e_4237_; lean_object* v___x_4239_; 
lean_dec_ref(v_post_4185_);
lean_dec_ref(v_e_4184_);
lean_dec_ref(v_pre_4183_);
v_e_4237_ = lean_ctor_get(v_a_4197_, 0);
lean_inc_ref(v_e_4237_);
lean_dec_ref_known(v_a_4197_, 1);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_e_4237_);
v___x_4239_ = v___x_4199_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_e_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
case 1:
{
lean_object* v_e_4241_; lean_object* v___x_4242_; 
lean_del_object(v___x_4199_);
lean_dec_ref(v_e_4184_);
v_e_4241_ = lean_ctor_get(v_a_4197_, 0);
lean_inc_ref(v_e_4241_);
lean_dec_ref_known(v_a_4197_, 1);
v___x_4242_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v_e_4241_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4242_;
}
default: 
{
lean_object* v_e_x3f_4243_; 
lean_del_object(v___x_4199_);
v_e_x3f_4243_ = lean_ctor_get(v_a_4197_, 0);
lean_inc(v_e_x3f_4243_);
lean_dec_ref_known(v_a_4197_, 1);
if (lean_obj_tag(v_e_x3f_4243_) == 0)
{
v___y_4202_ = v_e_4184_;
goto v___jp_4201_;
}
else
{
lean_object* v_val_4244_; 
lean_dec_ref(v_e_4184_);
v_val_4244_ = lean_ctor_get(v_e_x3f_4243_, 0);
lean_inc(v_val_4244_);
lean_dec_ref_known(v_e_x3f_4243_, 1);
v___y_4202_ = v_val_4244_;
goto v___jp_4201_;
}
}
}
v___jp_4201_:
{
switch(lean_obj_tag(v___y_4202_))
{
case 7:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___x_4203_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4204_;
}
case 6:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___x_4205_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4206_;
}
case 8:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___x_4207_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4208_;
}
case 5:
{
lean_object* v_dummy_4209_; lean_object* v_nargs_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_dummy_4209_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4210_ = l_Lean_Expr_getAppNumArgs(v___y_4202_);
lean_inc(v_nargs_4210_);
v___x_4211_ = lean_mk_array(v_nargs_4210_, v_dummy_4209_);
v___x_4212_ = lean_unsigned_to_nat(1u);
v___x_4213_ = lean_nat_sub(v_nargs_4210_, v___x_4212_);
lean_dec(v_nargs_4210_);
v___x_4214_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4188_, v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v___y_4202_, v___x_4211_, v___x_4213_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4214_;
}
case 10:
{
lean_object* v_data_4215_; lean_object* v_expr_4216_; lean_object* v___x_4217_; 
v_data_4215_ = lean_ctor_get(v___y_4202_, 0);
v_expr_4216_ = lean_ctor_get(v___y_4202_, 1);
lean_inc_ref(v_expr_4216_);
lean_inc_ref(v_post_4185_);
lean_inc_ref(v_pre_4183_);
v___x_4217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v_expr_4216_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; size_t v___x_4219_; size_t v___x_4220_; uint8_t v___x_4221_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
v___x_4219_ = lean_ptr_addr(v_expr_4216_);
v___x_4220_ = lean_ptr_addr(v_a_4218_);
v___x_4221_ = lean_usize_dec_eq(v___x_4219_, v___x_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
lean_inc(v_data_4215_);
lean_dec_ref_known(v___y_4202_, 2);
v___x_4222_ = l_Lean_Expr_mdata___override(v_data_4215_, v_a_4218_);
v___x_4223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___x_4222_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4223_;
}
else
{
lean_object* v___x_4224_; 
lean_dec(v_a_4218_);
v___x_4224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4224_;
}
}
else
{
lean_dec_ref_known(v___y_4202_, 2);
lean_dec_ref(v_post_4185_);
lean_dec_ref(v_pre_4183_);
return v___x_4217_;
}
}
case 11:
{
lean_object* v_typeName_4225_; lean_object* v_idx_4226_; lean_object* v_struct_4227_; lean_object* v___x_4228_; 
v_typeName_4225_ = lean_ctor_get(v___y_4202_, 0);
v_idx_4226_ = lean_ctor_get(v___y_4202_, 1);
v_struct_4227_ = lean_ctor_get(v___y_4202_, 2);
lean_inc_ref(v_struct_4227_);
lean_inc_ref(v_post_4185_);
lean_inc_ref(v_pre_4183_);
v___x_4228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v_struct_4227_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; size_t v___x_4230_; size_t v___x_4231_; uint8_t v___x_4232_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v___x_4230_ = lean_ptr_addr(v_struct_4227_);
v___x_4231_ = lean_ptr_addr(v_a_4229_);
v___x_4232_ = lean_usize_dec_eq(v___x_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_inc(v_idx_4226_);
lean_inc(v_typeName_4225_);
lean_dec_ref_known(v___y_4202_, 3);
v___x_4233_ = l_Lean_Expr_proj___override(v_typeName_4225_, v_idx_4226_, v_a_4229_);
v___x_4234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___x_4233_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4234_;
}
else
{
lean_object* v___x_4235_; 
lean_dec(v_a_4229_);
v___x_4235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4235_;
}
}
else
{
lean_dec_ref_known(v___y_4202_, 3);
lean_dec_ref(v_post_4185_);
lean_dec_ref(v_pre_4183_);
return v___x_4228_;
}
}
default: 
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4183_, v_post_4185_, v_usedLetOnly_4186_, v_skipConstInApp_4187_, v_skipInstances_4188_, v___y_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_post_4185_);
lean_dec_ref(v_e_4184_);
lean_dec_ref(v_pre_4183_);
v_a_4246_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4196_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4196_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec_ref(v_post_4185_);
lean_dec_ref(v_e_4184_);
lean_dec_ref(v_pre_4183_);
v_a_4254_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4195_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4195_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4262_, lean_object* v_pre_4263_, lean_object* v_e_4264_, lean_object* v_post_4265_, lean_object* v_usedLetOnly_4266_, lean_object* v_skipConstInApp_4267_, lean_object* v_skipInstances_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
uint8_t v_usedLetOnly_boxed_4275_; uint8_t v_skipConstInApp_boxed_4276_; uint8_t v_skipInstances_boxed_4277_; lean_object* v_res_4278_; 
v_usedLetOnly_boxed_4275_ = lean_unbox(v_usedLetOnly_4266_);
v_skipConstInApp_boxed_4276_ = lean_unbox(v_skipConstInApp_4267_);
v_skipInstances_boxed_4277_ = lean_unbox(v_skipInstances_4268_);
v_res_4278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4262_, v_pre_4263_, v_e_4264_, v_post_4265_, v_usedLetOnly_boxed_4275_, v_skipConstInApp_boxed_4276_, v_skipInstances_boxed_4277_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4279_, lean_object* v_post_4280_, uint8_t v_usedLetOnly_4281_, uint8_t v_skipConstInApp_4282_, uint8_t v_skipInstances_4283_, lean_object* v_e_4284_, lean_object* v_a_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
lean_inc(v_a_4285_);
v___x_4291_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4291_, 0, lean_box(0));
lean_closure_set(v___x_4291_, 1, lean_box(0));
lean_closure_set(v___x_4291_, 2, v_a_4285_);
v___x_4292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4291_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4327_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4327_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4327_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4293_, v_e_4284_);
lean_dec(v_a_4293_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; 
lean_del_object(v___x_4295_);
v___x_4298_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4299_ = lean_box(v_usedLetOnly_4281_);
v___x_4300_ = lean_box(v_skipConstInApp_4282_);
v___x_4301_ = lean_box(v_skipInstances_4283_);
lean_inc_ref(v_e_4284_);
v___f_4302_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4302_, 0, v___x_4298_);
lean_closure_set(v___f_4302_, 1, v_pre_4279_);
lean_closure_set(v___f_4302_, 2, v_e_4284_);
lean_closure_set(v___f_4302_, 3, v_post_4280_);
lean_closure_set(v___f_4302_, 4, v___x_4299_);
lean_closure_set(v___f_4302_, 5, v___x_4300_);
lean_closure_set(v___f_4302_, 6, v___x_4301_);
v___x_4303_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4302_, v_a_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___f_4305_; lean_object* v___x_4306_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc_n(v_a_4304_, 2);
lean_dec_ref_known(v___x_4303_, 1);
lean_inc(v_a_4285_);
v___f_4305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4305_, 0, v_a_4285_);
lean_closure_set(v___f_4305_, 1, v_e_4284_);
lean_closure_set(v___f_4305_, 2, v_a_4304_);
v___x_4306_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4305_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4313_ == 0)
{
lean_object* v_unused_4314_; 
v_unused_4314_ = lean_ctor_get(v___x_4306_, 0);
lean_dec(v_unused_4314_);
v___x_4308_ = v___x_4306_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_dec(v___x_4306_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v_a_4304_);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4304_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_a_4304_);
v_a_4315_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4306_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4306_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_dec_ref(v_e_4284_);
return v___x_4303_;
}
}
else
{
lean_object* v_val_4323_; lean_object* v___x_4325_; 
lean_dec_ref(v_e_4284_);
lean_dec_ref(v_post_4280_);
lean_dec_ref(v_pre_4279_);
v_val_4323_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_val_4323_);
lean_dec_ref_known(v___x_4297_, 1);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v_val_4323_);
v___x_4325_ = v___x_4295_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_val_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v_e_4284_);
lean_dec_ref(v_post_4280_);
lean_dec_ref(v_pre_4279_);
v_a_4328_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4292_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4292_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4336_, lean_object* v_post_4337_, uint8_t v_usedLetOnly_4338_, uint8_t v_skipConstInApp_4339_, uint8_t v_skipInstances_4340_, lean_object* v_fvars_4341_, lean_object* v_e_4342_, lean_object* v_a_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
if (lean_obj_tag(v_e_4342_) == 7)
{
lean_object* v_binderName_4349_; lean_object* v_binderType_4350_; lean_object* v_body_4351_; uint8_t v_binderInfo_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___f_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v_binderName_4349_ = lean_ctor_get(v_e_4342_, 0);
lean_inc(v_binderName_4349_);
v_binderType_4350_ = lean_ctor_get(v_e_4342_, 1);
lean_inc_ref(v_binderType_4350_);
v_body_4351_ = lean_ctor_get(v_e_4342_, 2);
lean_inc_ref(v_body_4351_);
v_binderInfo_4352_ = lean_ctor_get_uint8(v_e_4342_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4342_, 3);
v___x_4353_ = lean_box(v_usedLetOnly_4338_);
v___x_4354_ = lean_box(v_skipConstInApp_4339_);
v___x_4355_ = lean_box(v_skipInstances_4340_);
lean_inc_ref(v_post_4337_);
lean_inc_ref(v_pre_4336_);
lean_inc_ref(v_fvars_4341_);
v___f_4356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4356_, 0, v_fvars_4341_);
lean_closure_set(v___f_4356_, 1, v_pre_4336_);
lean_closure_set(v___f_4356_, 2, v_post_4337_);
lean_closure_set(v___f_4356_, 3, v___x_4353_);
lean_closure_set(v___f_4356_, 4, v___x_4354_);
lean_closure_set(v___f_4356_, 5, v___x_4355_);
lean_closure_set(v___f_4356_, 6, v_body_4351_);
v___x_4357_ = lean_expr_instantiate_rev(v_binderType_4350_, v_fvars_4341_);
lean_dec_ref(v_fvars_4341_);
lean_dec_ref(v_binderType_4350_);
v___x_4358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4336_, v_post_4337_, v_usedLetOnly_4338_, v_skipConstInApp_4339_, v_skipInstances_4340_, v___x_4357_, v_a_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = 0;
v___x_4361_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4349_, v_binderInfo_4352_, v_a_4359_, v___f_4356_, v___x_4360_, v_a_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
return v___x_4361_;
}
else
{
lean_dec_ref(v___f_4356_);
lean_dec(v_binderName_4349_);
return v___x_4358_;
}
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_expr_instantiate_rev(v_e_4342_, v_fvars_4341_);
lean_dec_ref(v_e_4342_);
lean_inc_ref(v_post_4337_);
lean_inc_ref(v_pre_4336_);
v___x_4363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4336_, v_post_4337_, v_usedLetOnly_4338_, v_skipConstInApp_4339_, v_skipInstances_4340_, v___x_4362_, v_a_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; uint8_t v___x_4365_; uint8_t v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = 0;
v___x_4366_ = 1;
v___x_4367_ = 1;
v___x_4368_ = l_Lean_Meta_mkForallFVars(v_fvars_4341_, v_a_4364_, v___x_4365_, v_usedLetOnly_4338_, v___x_4366_, v___x_4367_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec_ref(v_fvars_4341_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4336_, v_post_4337_, v_usedLetOnly_4338_, v_skipConstInApp_4339_, v_skipInstances_4340_, v_a_4369_, v_a_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
return v___x_4370_;
}
else
{
lean_dec_ref(v_post_4337_);
lean_dec_ref(v_pre_4336_);
return v___x_4368_;
}
}
else
{
lean_dec_ref(v_fvars_4341_);
lean_dec_ref(v_post_4337_);
lean_dec_ref(v_pre_4336_);
return v___x_4363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4371_, lean_object* v_pre_4372_, lean_object* v_post_4373_, uint8_t v_usedLetOnly_4374_, uint8_t v_skipConstInApp_4375_, uint8_t v_skipInstances_4376_, lean_object* v_body_4377_, lean_object* v_x_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_array_push(v_fvars_4371_, v_x_4378_);
v___x_4386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4372_, v_post_4373_, v_usedLetOnly_4374_, v_skipConstInApp_4375_, v_skipInstances_4376_, v___x_4385_, v_body_4377_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4387_, lean_object* v_post_4388_, lean_object* v_usedLetOnly_4389_, lean_object* v_skipConstInApp_4390_, lean_object* v_skipInstances_4391_, lean_object* v_e_4392_, lean_object* v_a_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v_usedLetOnly_boxed_4399_; uint8_t v_skipConstInApp_boxed_4400_; uint8_t v_skipInstances_boxed_4401_; lean_object* v_res_4402_; 
v_usedLetOnly_boxed_4399_ = lean_unbox(v_usedLetOnly_4389_);
v_skipConstInApp_boxed_4400_ = lean_unbox(v_skipConstInApp_4390_);
v_skipInstances_boxed_4401_ = lean_unbox(v_skipInstances_4391_);
v_res_4402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4387_, v_post_4388_, v_usedLetOnly_boxed_4399_, v_skipConstInApp_boxed_4400_, v_skipInstances_boxed_4401_, v_e_4392_, v_a_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v_a_4393_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4403_, lean_object* v_post_4404_, lean_object* v_usedLetOnly_4405_, lean_object* v_skipConstInApp_4406_, lean_object* v_skipInstances_4407_, lean_object* v_sz_4408_, lean_object* v_i_4409_, lean_object* v_bs_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v_usedLetOnly_boxed_4417_; uint8_t v_skipConstInApp_boxed_4418_; uint8_t v_skipInstances_boxed_4419_; size_t v_sz_boxed_4420_; size_t v_i_boxed_4421_; lean_object* v_res_4422_; 
v_usedLetOnly_boxed_4417_ = lean_unbox(v_usedLetOnly_4405_);
v_skipConstInApp_boxed_4418_ = lean_unbox(v_skipConstInApp_4406_);
v_skipInstances_boxed_4419_ = lean_unbox(v_skipInstances_4407_);
v_sz_boxed_4420_ = lean_unbox_usize(v_sz_4408_);
lean_dec(v_sz_4408_);
v_i_boxed_4421_ = lean_unbox_usize(v_i_4409_);
lean_dec(v_i_4409_);
v_res_4422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4403_, v_post_4404_, v_usedLetOnly_boxed_4417_, v_skipConstInApp_boxed_4418_, v_skipInstances_boxed_4419_, v_sz_boxed_4420_, v_i_boxed_4421_, v_bs_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4423_, lean_object* v_post_4424_, lean_object* v_usedLetOnly_4425_, lean_object* v_skipConstInApp_4426_, lean_object* v_skipInstances_4427_, lean_object* v_e_4428_, lean_object* v_a_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v_usedLetOnly_boxed_4435_; uint8_t v_skipConstInApp_boxed_4436_; uint8_t v_skipInstances_boxed_4437_; lean_object* v_res_4438_; 
v_usedLetOnly_boxed_4435_ = lean_unbox(v_usedLetOnly_4425_);
v_skipConstInApp_boxed_4436_ = lean_unbox(v_skipConstInApp_4426_);
v_skipInstances_boxed_4437_ = lean_unbox(v_skipInstances_4427_);
v_res_4438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4423_, v_post_4424_, v_usedLetOnly_boxed_4435_, v_skipConstInApp_boxed_4436_, v_skipInstances_boxed_4437_, v_e_4428_, v_a_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v_a_4429_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4439_, lean_object* v_post_4440_, lean_object* v_usedLetOnly_4441_, lean_object* v_skipConstInApp_4442_, lean_object* v_skipInstances_4443_, lean_object* v_fvars_4444_, lean_object* v_e_4445_, lean_object* v_a_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
uint8_t v_usedLetOnly_boxed_4452_; uint8_t v_skipConstInApp_boxed_4453_; uint8_t v_skipInstances_boxed_4454_; lean_object* v_res_4455_; 
v_usedLetOnly_boxed_4452_ = lean_unbox(v_usedLetOnly_4441_);
v_skipConstInApp_boxed_4453_ = lean_unbox(v_skipConstInApp_4442_);
v_skipInstances_boxed_4454_ = lean_unbox(v_skipInstances_4443_);
v_res_4455_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4439_, v_post_4440_, v_usedLetOnly_boxed_4452_, v_skipConstInApp_boxed_4453_, v_skipInstances_boxed_4454_, v_fvars_4444_, v_e_4445_, v_a_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_a_4446_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4456_, lean_object* v_post_4457_, lean_object* v_usedLetOnly_4458_, lean_object* v_skipConstInApp_4459_, lean_object* v_skipInstances_4460_, lean_object* v_fvars_4461_, lean_object* v_e_4462_, lean_object* v_a_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
uint8_t v_usedLetOnly_boxed_4469_; uint8_t v_skipConstInApp_boxed_4470_; uint8_t v_skipInstances_boxed_4471_; lean_object* v_res_4472_; 
v_usedLetOnly_boxed_4469_ = lean_unbox(v_usedLetOnly_4458_);
v_skipConstInApp_boxed_4470_ = lean_unbox(v_skipConstInApp_4459_);
v_skipInstances_boxed_4471_ = lean_unbox(v_skipInstances_4460_);
v_res_4472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4456_, v_post_4457_, v_usedLetOnly_boxed_4469_, v_skipConstInApp_boxed_4470_, v_skipInstances_boxed_4471_, v_fvars_4461_, v_e_4462_, v_a_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v_a_4463_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4473_, lean_object* v_post_4474_, lean_object* v_usedLetOnly_4475_, lean_object* v_skipConstInApp_4476_, lean_object* v_skipInstances_4477_, lean_object* v_fvars_4478_, lean_object* v_e_4479_, lean_object* v_a_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
uint8_t v_usedLetOnly_boxed_4486_; uint8_t v_skipConstInApp_boxed_4487_; uint8_t v_skipInstances_boxed_4488_; lean_object* v_res_4489_; 
v_usedLetOnly_boxed_4486_ = lean_unbox(v_usedLetOnly_4475_);
v_skipConstInApp_boxed_4487_ = lean_unbox(v_skipConstInApp_4476_);
v_skipInstances_boxed_4488_ = lean_unbox(v_skipInstances_4477_);
v_res_4489_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4473_, v_post_4474_, v_usedLetOnly_boxed_4486_, v_skipConstInApp_boxed_4487_, v_skipInstances_boxed_4488_, v_fvars_4478_, v_e_4479_, v_a_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v_a_4480_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4490_, lean_object* v___x_4491_, lean_object* v_pre_4492_, lean_object* v_post_4493_, lean_object* v_usedLetOnly_4494_, lean_object* v_skipConstInApp_4495_, lean_object* v_skipInstances_4496_, lean_object* v_a_4497_, lean_object* v_b_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
uint8_t v_usedLetOnly_boxed_4505_; uint8_t v_skipConstInApp_boxed_4506_; uint8_t v_skipInstances_boxed_4507_; lean_object* v_res_4508_; 
v_usedLetOnly_boxed_4505_ = lean_unbox(v_usedLetOnly_4494_);
v_skipConstInApp_boxed_4506_ = lean_unbox(v_skipConstInApp_4495_);
v_skipInstances_boxed_4507_ = lean_unbox(v_skipInstances_4496_);
v_res_4508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4490_, v___x_4491_, v_pre_4492_, v_post_4493_, v_usedLetOnly_boxed_4505_, v_skipConstInApp_boxed_4506_, v_skipInstances_boxed_4507_, v_a_4497_, v_b_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___x_4491_);
lean_dec(v_upperBound_4490_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4509_, lean_object* v_pre_4510_, lean_object* v_post_4511_, lean_object* v_usedLetOnly_4512_, lean_object* v_skipConstInApp_4513_, lean_object* v_x_4514_, lean_object* v_x_4515_, lean_object* v_x_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
uint8_t v_skipInstances_boxed_4523_; uint8_t v_usedLetOnly_boxed_4524_; uint8_t v_skipConstInApp_boxed_4525_; lean_object* v_res_4526_; 
v_skipInstances_boxed_4523_ = lean_unbox(v_skipInstances_4509_);
v_usedLetOnly_boxed_4524_ = lean_unbox(v_usedLetOnly_4512_);
v_skipConstInApp_boxed_4525_ = lean_unbox(v_skipConstInApp_4513_);
v_res_4526_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4523_, v_pre_4510_, v_post_4511_, v_usedLetOnly_boxed_4524_, v_skipConstInApp_boxed_4525_, v_x_4514_, v_x_4515_, v_x_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4527_, lean_object* v_pre_4528_, lean_object* v_post_4529_, uint8_t v_usedLetOnly_4530_, uint8_t v_skipConstInApp_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v_a_4540_; lean_object* v___x_4541_; 
v___x_4537_ = 0;
v___x_4538_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4539_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4538_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
lean_dec_ref(v___x_4539_);
v___x_4541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4528_, v_post_4529_, v_usedLetOnly_4530_, v_skipConstInApp_4531_, v___x_4537_, v_input_4527_, v_a_4540_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4543_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4543_, 0, lean_box(0));
lean_closure_set(v___x_4543_, 1, lean_box(0));
lean_closure_set(v___x_4543_, 2, v_a_4540_);
v___x_4544_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4543_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v___x_4544_, 0);
lean_dec(v_unused_4552_);
v___x_4546_ = v___x_4544_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_dec(v___x_4544_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v_a_4542_);
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4542_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
else
{
lean_dec(v_a_4540_);
return v___x_4541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4553_, lean_object* v_pre_4554_, lean_object* v_post_4555_, lean_object* v_usedLetOnly_4556_, lean_object* v_skipConstInApp_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
uint8_t v_usedLetOnly_boxed_4563_; uint8_t v_skipConstInApp_boxed_4564_; lean_object* v_res_4565_; 
v_usedLetOnly_boxed_4563_ = lean_unbox(v_usedLetOnly_4556_);
v_skipConstInApp_boxed_4564_ = lean_unbox(v_skipConstInApp_4557_);
v_res_4565_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4553_, v_pre_4554_, v_post_4555_, v_usedLetOnly_boxed_4563_, v_skipConstInApp_boxed_4564_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4567_, uint8_t v_zetaDelta_4568_, uint8_t v_zetaHave_4569_, uint8_t v_beta_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v_lctx_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___f_4580_; uint8_t v___x_4581_; 
v_lctx_4576_ = lean_ctor_get(v_a_4571_, 2);
lean_inc_ref(v_lctx_4576_);
v___x_4577_ = lean_local_ctx_num_indices(v_lctx_4576_);
v___x_4578_ = lean_box(v_zetaHave_4569_);
v___x_4579_ = lean_box(v_zetaDelta_4568_);
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4580_, 0, v___x_4578_);
lean_closure_set(v___f_4580_, 1, v___x_4577_);
lean_closure_set(v___f_4580_, 2, v___x_4579_);
v___x_4581_ = 1;
if (v_beta_4570_ == 0)
{
lean_object* v___f_4582_; lean_object* v___f_4583_; lean_object* v___x_4584_; 
v___f_4582_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4583_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4583_, 0, v___f_4580_);
v___x_4584_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4567_, v___f_4583_, v___f_4582_, v___x_4581_, v_beta_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4584_;
}
else
{
lean_object* v___f_4585_; lean_object* v___f_4586_; uint8_t v___x_4587_; lean_object* v___x_4588_; 
v___f_4585_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4586_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4586_, 0, v___f_4580_);
v___x_4587_ = 0;
v___x_4588_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4567_, v___f_4586_, v___f_4585_, v___x_4581_, v___x_4587_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4589_, lean_object* v_zetaDelta_4590_, lean_object* v_zetaHave_4591_, lean_object* v_beta_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
uint8_t v_zetaDelta_boxed_4598_; uint8_t v_zetaHave_boxed_4599_; uint8_t v_beta_boxed_4600_; lean_object* v_res_4601_; 
v_zetaDelta_boxed_4598_ = lean_unbox(v_zetaDelta_4590_);
v_zetaHave_boxed_4599_ = lean_unbox(v_zetaHave_4591_);
v_beta_boxed_4600_ = lean_unbox(v_beta_4592_);
v_res_4601_ = l_Lean_Meta_zetaReduce(v_e_4589_, v_zetaDelta_boxed_4598_, v_zetaHave_boxed_4599_, v_beta_boxed_4600_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4602_, lean_object* v___x_4603_, lean_object* v_pre_4604_, lean_object* v_post_4605_, uint8_t v_usedLetOnly_4606_, uint8_t v_skipConstInApp_4607_, uint8_t v_skipInstances_4608_, lean_object* v___x_4609_, lean_object* v_inst_4610_, lean_object* v_R_4611_, lean_object* v_a_4612_, lean_object* v_b_4613_, lean_object* v_c_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4602_, v___x_4603_, v_pre_4604_, v_post_4605_, v_usedLetOnly_4606_, v_skipConstInApp_4607_, v_skipInstances_4608_, v_a_4612_, v_b_4613_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4622_ = _args[0];
lean_object* v___x_4623_ = _args[1];
lean_object* v_pre_4624_ = _args[2];
lean_object* v_post_4625_ = _args[3];
lean_object* v_usedLetOnly_4626_ = _args[4];
lean_object* v_skipConstInApp_4627_ = _args[5];
lean_object* v_skipInstances_4628_ = _args[6];
lean_object* v___x_4629_ = _args[7];
lean_object* v_inst_4630_ = _args[8];
lean_object* v_R_4631_ = _args[9];
lean_object* v_a_4632_ = _args[10];
lean_object* v_b_4633_ = _args[11];
lean_object* v_c_4634_ = _args[12];
lean_object* v___y_4635_ = _args[13];
lean_object* v___y_4636_ = _args[14];
lean_object* v___y_4637_ = _args[15];
lean_object* v___y_4638_ = _args[16];
lean_object* v___y_4639_ = _args[17];
lean_object* v___y_4640_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4641_; uint8_t v_skipConstInApp_boxed_4642_; uint8_t v_skipInstances_boxed_4643_; lean_object* v_res_4644_; 
v_usedLetOnly_boxed_4641_ = lean_unbox(v_usedLetOnly_4626_);
v_skipConstInApp_boxed_4642_ = lean_unbox(v_skipConstInApp_4627_);
v_skipInstances_boxed_4643_ = lean_unbox(v_skipInstances_4628_);
v_res_4644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4622_, v___x_4623_, v_pre_4624_, v_post_4625_, v_usedLetOnly_boxed_4641_, v_skipConstInApp_boxed_4642_, v_skipInstances_boxed_4643_, v___x_4629_, v_inst_4630_, v_R_4631_, v_a_4632_, v_b_4633_, v_c_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec(v___x_4629_);
lean_dec_ref(v___x_4623_);
lean_dec(v_upperBound_4622_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4645_, lean_object* v_name_4646_, uint8_t v_bi_4647_, lean_object* v_type_4648_, lean_object* v_k_4649_, uint8_t v_kind_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4646_, v_bi_4647_, v_type_4648_, v_k_4649_, v_kind_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4658_, lean_object* v_name_4659_, lean_object* v_bi_4660_, lean_object* v_type_4661_, lean_object* v_k_4662_, lean_object* v_kind_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
uint8_t v_bi_boxed_4670_; uint8_t v_kind_boxed_4671_; lean_object* v_res_4672_; 
v_bi_boxed_4670_ = lean_unbox(v_bi_4660_);
v_kind_boxed_4671_ = lean_unbox(v_kind_4663_);
v_res_4672_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4658_, v_name_4659_, v_bi_boxed_4670_, v_type_4661_, v_k_4662_, v_kind_boxed_4671_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4673_, lean_object* v_name_4674_, lean_object* v_type_4675_, lean_object* v_val_4676_, lean_object* v_k_4677_, uint8_t v_nondep_4678_, uint8_t v_kind_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4674_, v_type_4675_, v_val_4676_, v_k_4677_, v_nondep_4678_, v_kind_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4687_, lean_object* v_name_4688_, lean_object* v_type_4689_, lean_object* v_val_4690_, lean_object* v_k_4691_, lean_object* v_nondep_4692_, lean_object* v_kind_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
uint8_t v_nondep_boxed_4700_; uint8_t v_kind_boxed_4701_; lean_object* v_res_4702_; 
v_nondep_boxed_4700_ = lean_unbox(v_nondep_4692_);
v_kind_boxed_4701_ = lean_unbox(v_kind_4693_);
v_res_4702_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4687_, v_name_4688_, v_type_4689_, v_val_4690_, v_k_4691_, v_nondep_boxed_4700_, v_kind_boxed_4701_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4703_, lean_object* v_ref_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4704_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4711_, lean_object* v_ref_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4711_, v_ref_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4719_, lean_object* v_x_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4728_, lean_object* v_x_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4728_, v_x_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
return v_res_4736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4737_, lean_object* v_as_4738_, size_t v_i_4739_, size_t v_stop_4740_){
_start:
{
uint8_t v___x_4741_; 
v___x_4741_ = lean_usize_dec_eq(v_i_4739_, v_stop_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; uint8_t v___x_4743_; 
v___x_4742_ = lean_array_uget_borrowed(v_as_4738_, v_i_4739_);
v___x_4743_ = l_Lean_instBEqFVarId_beq(v_a_4737_, v___x_4742_);
if (v___x_4743_ == 0)
{
size_t v___x_4744_; size_t v___x_4745_; 
v___x_4744_ = ((size_t)1ULL);
v___x_4745_ = lean_usize_add(v_i_4739_, v___x_4744_);
v_i_4739_ = v___x_4745_;
goto _start;
}
else
{
return v___x_4743_;
}
}
else
{
uint8_t v___x_4747_; 
v___x_4747_ = 0;
return v___x_4747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4748_, lean_object* v_as_4749_, lean_object* v_i_4750_, lean_object* v_stop_4751_){
_start:
{
size_t v_i_boxed_4752_; size_t v_stop_boxed_4753_; uint8_t v_res_4754_; lean_object* v_r_4755_; 
v_i_boxed_4752_ = lean_unbox_usize(v_i_4750_);
lean_dec(v_i_4750_);
v_stop_boxed_4753_ = lean_unbox_usize(v_stop_4751_);
lean_dec(v_stop_4751_);
v_res_4754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4748_, v_as_4749_, v_i_boxed_4752_, v_stop_boxed_4753_);
lean_dec_ref(v_as_4749_);
lean_dec(v_a_4748_);
v_r_4755_ = lean_box(v_res_4754_);
return v_r_4755_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = lean_array_get_size(v_as_4756_);
v___x_4760_ = lean_nat_dec_lt(v___x_4758_, v___x_4759_);
if (v___x_4760_ == 0)
{
return v___x_4760_;
}
else
{
size_t v___x_4761_; size_t v___x_4762_; uint8_t v___x_4763_; 
v___x_4761_ = ((size_t)0ULL);
v___x_4762_ = lean_usize_of_nat(v___x_4759_);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4757_, v_as_4756_, v___x_4761_, v___x_4762_);
return v___x_4763_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4764_, lean_object* v_a_4765_){
_start:
{
uint8_t v_res_4766_; lean_object* v_r_4767_; 
v_res_4766_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_as_4764_);
v_r_4767_ = lean_box(v_res_4766_);
return v_r_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4768_, lean_object* v_e_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_Expr_getAppFn(v_e_4769_);
if (lean_obj_tag(v___x_4778_) == 1)
{
lean_object* v_fvarId_4779_; uint8_t v___x_4780_; 
v_fvarId_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_fvarId_4779_);
lean_dec_ref_known(v___x_4778_, 1);
v___x_4780_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4768_, v_fvarId_4779_);
if (v___x_4780_ == 0)
{
lean_dec(v_fvarId_4779_);
lean_dec_ref(v_e_4769_);
goto v___jp_4775_;
}
else
{
uint8_t v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = 0;
v___x_4782_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4779_, v___x_4781_, v___y_4770_, v___y_4772_, v___y_4773_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref_known(v___x_4782_, 1);
if (lean_obj_tag(v_a_4783_) == 1)
{
lean_object* v_val_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4807_; 
v_val_4784_ = lean_ctor_get(v_a_4783_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_a_4783_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4786_ = v_a_4783_;
v_isShared_4787_ = v_isSharedCheck_4807_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_val_4784_);
lean_dec(v_a_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4807_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4806_; 
v___x_4788_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4784_, v___y_4771_);
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4806_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4806_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v_dummy_4793_; lean_object* v_nargs_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v_dummy_4793_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4794_ = l_Lean_Expr_getAppNumArgs(v_e_4769_);
lean_inc(v_nargs_4794_);
v___x_4795_ = lean_mk_array(v_nargs_4794_, v_dummy_4793_);
v___x_4796_ = lean_unsigned_to_nat(1u);
v___x_4797_ = lean_nat_sub(v_nargs_4794_, v___x_4796_);
lean_dec(v_nargs_4794_);
v___x_4798_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4769_, v___x_4795_, v___x_4797_);
v___x_4799_ = l_Lean_Expr_beta(v_a_4789_, v___x_4798_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4799_);
v___x_4801_ = v___x_4786_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4803_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4801_);
v___x_4803_ = v___x_4791_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
else
{
lean_dec(v_a_4783_);
lean_dec_ref(v_e_4769_);
goto v___jp_4775_;
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec_ref(v_e_4769_);
v_a_4808_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4782_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4782_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
else
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_dec_ref(v___x_4778_);
lean_dec_ref(v_e_4769_);
v___x_4816_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
return v___x_4817_;
}
v___jp_4775_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4818_, lean_object* v_e_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4818_, v_e_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec_ref(v_fvars_4818_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4826_, lean_object* v_fvars_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v___f_4833_; lean_object* v_pre_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; 
v___f_4833_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4834_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4834_, 0, v_fvars_4827_);
v___x_4835_ = 0;
v___x_4836_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4826_, v_pre_4834_, v___f_4833_, v___x_4835_, v___x_4835_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4837_, lean_object* v_fvars_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Meta_zetaDeltaFVars(v_e_4837_, v_fvars_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
return v_res_4844_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4845_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
return v___x_4847_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; lean_object* v_nextMacroScope_4854_; lean_object* v_ngen_4855_; lean_object* v_auxDeclNGen_4856_; lean_object* v_traceState_4857_; lean_object* v_recordedDeps_4858_; lean_object* v_messages_4859_; lean_object* v_infoState_4860_; lean_object* v_snapshotTasks_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4872_; 
v___x_4853_ = lean_st_ref_take(v___y_4851_);
v_nextMacroScope_4854_ = lean_ctor_get(v___x_4853_, 1);
v_ngen_4855_ = lean_ctor_get(v___x_4853_, 2);
v_auxDeclNGen_4856_ = lean_ctor_get(v___x_4853_, 3);
v_traceState_4857_ = lean_ctor_get(v___x_4853_, 4);
v_recordedDeps_4858_ = lean_ctor_get(v___x_4853_, 6);
v_messages_4859_ = lean_ctor_get(v___x_4853_, 7);
v_infoState_4860_ = lean_ctor_get(v___x_4853_, 8);
v_snapshotTasks_4861_ = lean_ctor_get(v___x_4853_, 9);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4872_ == 0)
{
lean_object* v_unused_4873_; lean_object* v_unused_4874_; 
v_unused_4873_ = lean_ctor_get(v___x_4853_, 5);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v___x_4853_, 0);
lean_dec(v_unused_4874_);
v___x_4863_ = v___x_4853_;
v_isShared_4864_ = v_isSharedCheck_4872_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_snapshotTasks_4861_);
lean_inc(v_infoState_4860_);
lean_inc(v_messages_4859_);
lean_inc(v_recordedDeps_4858_);
lean_inc(v_traceState_4857_);
lean_inc(v_auxDeclNGen_4856_);
lean_inc(v_ngen_4855_);
lean_inc(v_nextMacroScope_4854_);
lean_dec(v___x_4853_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4872_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 5, v___x_4866_);
lean_ctor_set(v___x_4863_, 0, v_env_4850_);
v___x_4868_ = v___x_4863_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_env_4850_);
lean_ctor_set(v_reuseFailAlloc_4871_, 1, v_nextMacroScope_4854_);
lean_ctor_set(v_reuseFailAlloc_4871_, 2, v_ngen_4855_);
lean_ctor_set(v_reuseFailAlloc_4871_, 3, v_auxDeclNGen_4856_);
lean_ctor_set(v_reuseFailAlloc_4871_, 4, v_traceState_4857_);
lean_ctor_set(v_reuseFailAlloc_4871_, 5, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4871_, 6, v_recordedDeps_4858_);
lean_ctor_set(v_reuseFailAlloc_4871_, 7, v_messages_4859_);
lean_ctor_set(v_reuseFailAlloc_4871_, 8, v_infoState_4860_);
lean_ctor_set(v_reuseFailAlloc_4871_, 9, v_snapshotTasks_4861_);
v___x_4868_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_st_ref_put(v___y_4851_, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4865_);
return v___x_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4875_, v___y_4876_);
lean_dec(v___y_4876_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v___x_4883_; 
v___x_4883_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4879_, v___y_4881_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4884_, v___y_4885_, v___y_4886_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4889_, lean_object* v___x_4890_, uint8_t v___x_4891_, lean_object* v_e_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
if (lean_obj_tag(v_e_4892_) == 4)
{
lean_object* v_declName_4896_; lean_object* v_us_4897_; uint8_t v___x_4898_; uint8_t v___x_4899_; 
v_declName_4896_ = lean_ctor_get(v_e_4892_, 0);
v_us_4897_ = lean_ctor_get(v_e_4892_, 1);
v___x_4898_ = 1;
lean_inc(v_declName_4896_);
v___x_4899_ = l_Lean_Environment_contains(v_env_4889_, v_declName_4896_, v___x_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; 
lean_inc(v_declName_4896_);
v___x_4900_ = l_Lean_Environment_find_x3f(v___x_4890_, v_declName_4896_, v___x_4891_);
if (lean_obj_tag(v___x_4900_) == 1)
{
lean_object* v_val_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4930_; 
v_val_4901_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4903_ = v___x_4900_;
v_isShared_4904_ = v_isSharedCheck_4930_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_val_4901_);
lean_dec(v___x_4900_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4930_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
uint8_t v___x_4905_; 
v___x_4905_ = l_Lean_ConstantInfo_hasValue(v_val_4901_, v___x_4898_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4907_; 
lean_dec(v_val_4901_);
if (v_isShared_4904_ == 0)
{
lean_ctor_set_tag(v___x_4903_, 0);
lean_ctor_set(v___x_4903_, 0, v_e_4892_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_e_4892_);
v___x_4907_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
return v___x_4908_;
}
}
else
{
lean_object* v___x_4910_; 
lean_inc(v_us_4897_);
lean_dec_ref_known(v_e_4892_, 2);
v___x_4910_ = l_Lean_Core_instantiateValueLevelParams(v_val_4901_, v_us_4897_, v___x_4898_, v___y_4893_, v___y_4894_);
lean_dec(v_val_4901_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4921_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4913_ = v___x_4910_;
v_isShared_4914_ = v_isSharedCheck_4921_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4921_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 0, v_a_4911_);
v___x_4916_ = v___x_4903_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4918_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4916_);
v___x_4918_ = v___x_4913_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_del_object(v___x_4903_);
v_a_4922_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4910_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4910_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
}
else
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
lean_dec(v___x_4900_);
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v_e_4892_);
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
return v___x_4932_;
}
}
else
{
lean_object* v___x_4933_; lean_object* v___x_4934_; 
lean_dec_ref(v___x_4890_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v_e_4892_);
v___x_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
return v___x_4934_;
}
}
else
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
lean_dec_ref(v_e_4892_);
lean_dec_ref(v___x_4890_);
lean_dec_ref(v_env_4889_);
v___x_4935_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4935_);
return v___x_4936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v_e_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
uint8_t v___x_1999__boxed_4944_; lean_object* v_res_4945_; 
v___x_1999__boxed_4944_ = lean_unbox(v___x_4939_);
v_res_4945_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4937_, v___x_4938_, v___x_1999__boxed_4944_, v_e_4940_, v___y_4941_, v___y_4942_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4946_, lean_object* v_e_4947_, lean_object* v___f_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; lean_object* v_env_4953_; uint8_t v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___f_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4952_ = lean_st_ref_get(v___y_4950_);
v_env_4953_ = lean_ctor_get(v___x_4952_, 0);
lean_inc_ref(v_env_4953_);
lean_dec(v___x_4952_);
v___x_4954_ = 0;
v___x_4955_ = l_Lean_Environment_setExporting(v_biggerEnv_4946_, v___x_4954_);
v___x_4956_ = lean_box(v___x_4954_);
lean_inc_ref(v___x_4955_);
v___f_4957_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4957_, 0, v_env_4953_);
lean_closure_set(v___f_4957_, 1, v___x_4955_);
lean_closure_set(v___f_4957_, 2, v___x_4956_);
v___x_4958_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4955_, v___y_4950_);
lean_dec_ref(v___x_4958_);
v___x_4959_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4947_, v___f_4957_, v___f_4948_, v___y_4949_, v___y_4950_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4960_, lean_object* v_e_4961_, lean_object* v___f_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4960_, v_e_4961_, v___f_4962_, v___y_4963_, v___y_4964_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4967_, lean_object* v_x_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
lean_object* v___x_4972_; lean_object* v_env_4973_; lean_object* v_a_4975_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4972_ = lean_st_ref_get(v___y_4970_);
v_env_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc_ref(v_env_4973_);
lean_dec(v___x_4972_);
v___x_4985_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4967_, v___y_4970_);
lean_dec_ref(v___x_4985_);
lean_inc(v___y_4970_);
lean_inc_ref(v___y_4969_);
v___x_4986_ = lean_apply_3(v_x_4968_, v___y_4969_, v___y_4970_, lean_box(0));
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4973_, v___y_4970_);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_4995_ == 0)
{
lean_object* v_unused_4996_; 
v_unused_4996_ = lean_ctor_get(v___x_4988_, 0);
lean_dec(v_unused_4996_);
v___x_4990_ = v___x_4988_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_dec(v___x_4988_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 0, v_a_4987_);
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4987_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
else
{
lean_object* v_a_4997_; 
v_a_4997_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4986_, 1);
v_a_4975_ = v_a_4997_;
goto v___jp_4974_;
}
v___jp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
v___x_4976_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4973_, v___y_4970_);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4983_ == 0)
{
lean_object* v_unused_4984_; 
v_unused_4984_ = lean_ctor_get(v___x_4976_, 0);
lean_dec(v_unused_4984_);
v___x_4978_ = v___x_4976_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_dec(v___x_4976_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
lean_ctor_set_tag(v___x_4978_, 1);
lean_ctor_set(v___x_4978_, 0, v_a_4975_);
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4975_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4998_, lean_object* v_x_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4998_, v_x_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5004_, lean_object* v_e_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___f_5009_; lean_object* v___f_5010_; lean_object* v___x_5011_; lean_object* v_env_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___f_5009_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5010_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5010_, 0, v_biggerEnv_5004_);
lean_closure_set(v___f_5010_, 1, v_e_5005_);
lean_closure_set(v___f_5010_, 2, v___f_5009_);
v___x_5011_ = lean_st_ref_get(v_a_5007_);
v_env_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc_ref(v_env_5012_);
lean_dec(v___x_5011_);
v___x_5013_ = l_Lean_Environment_unlockAsync(v_env_5012_);
v___x_5014_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5013_, v___f_5010_, v_a_5006_, v_a_5007_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5015_, lean_object* v_e_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5015_, v_e_5016_, v_a_5017_, v_a_5018_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5021_, lean_object* v_env_5022_, lean_object* v_x_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5022_, v_x_5023_, v___y_5024_, v___y_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5028_, lean_object* v_env_5029_, lean_object* v_x_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5028_, v_env_5029_, v_x_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
return v_res_5034_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5035_, lean_object* v_axs_5036_, lean_object* v_numSectionVars_5037_, lean_object* v_as_5038_, size_t v_i_5039_, size_t v_stop_5040_){
_start:
{
uint8_t v___x_5045_; 
v___x_5045_ = lean_usize_dec_eq(v_i_5039_, v_stop_5040_);
if (v___x_5045_ == 0)
{
lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v___x_5046_ = lean_array_uget_borrowed(v_as_5038_, v_i_5039_);
v___x_5047_ = l_Lean_Expr_constName_x21(v_af_5035_);
v___x_5048_ = lean_name_eq(v___x_5047_, v___x_5046_);
lean_dec(v___x_5047_);
if (v___x_5048_ == 0)
{
goto v___jp_5041_;
}
else
{
lean_object* v___x_5049_; uint8_t v___x_5050_; 
v___x_5049_ = lean_array_get_size(v_axs_5036_);
v___x_5050_ = lean_nat_dec_le(v___x_5049_, v_numSectionVars_5037_);
if (v___x_5050_ == 0)
{
goto v___jp_5041_;
}
else
{
return v___x_5050_;
}
}
}
else
{
uint8_t v___x_5051_; 
v___x_5051_ = 0;
return v___x_5051_;
}
v___jp_5041_:
{
size_t v___x_5042_; size_t v___x_5043_; 
v___x_5042_ = ((size_t)1ULL);
v___x_5043_ = lean_usize_add(v_i_5039_, v___x_5042_);
v_i_5039_ = v___x_5043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5052_, lean_object* v_axs_5053_, lean_object* v_numSectionVars_5054_, lean_object* v_as_5055_, lean_object* v_i_5056_, lean_object* v_stop_5057_){
_start:
{
size_t v_i_boxed_5058_; size_t v_stop_boxed_5059_; uint8_t v_res_5060_; lean_object* v_r_5061_; 
v_i_boxed_5058_ = lean_unbox_usize(v_i_5056_);
lean_dec(v_i_5056_);
v_stop_boxed_5059_ = lean_unbox_usize(v_stop_5057_);
lean_dec(v_stop_5057_);
v_res_5060_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5052_, v_axs_5053_, v_numSectionVars_5054_, v_as_5055_, v_i_boxed_5058_, v_stop_boxed_5059_);
lean_dec_ref(v_as_5055_);
lean_dec(v_numSectionVars_5054_);
lean_dec_ref(v_axs_5053_);
lean_dec_ref(v_af_5052_);
v_r_5061_ = lean_box(v_res_5060_);
return v_r_5061_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5062_, lean_object* v_numSectionVars_5063_, lean_object* v_x_5064_, lean_object* v_x_5065_, lean_object* v_x_5066_){
_start:
{
if (lean_obj_tag(v_x_5064_) == 5)
{
lean_object* v_fn_5067_; lean_object* v_arg_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v_fn_5067_ = lean_ctor_get(v_x_5064_, 0);
lean_inc_ref(v_fn_5067_);
v_arg_5068_ = lean_ctor_get(v_x_5064_, 1);
lean_inc_ref(v_arg_5068_);
lean_dec_ref_known(v_x_5064_, 2);
v___x_5069_ = lean_array_set(v_x_5065_, v_x_5066_, v_arg_5068_);
v___x_5070_ = lean_unsigned_to_nat(1u);
v___x_5071_ = lean_nat_sub(v_x_5066_, v___x_5070_);
lean_dec(v_x_5066_);
v_x_5064_ = v_fn_5067_;
v_x_5065_ = v___x_5069_;
v_x_5066_ = v___x_5071_;
goto _start;
}
else
{
uint8_t v___x_5073_; 
lean_dec(v_x_5066_);
v___x_5073_ = l_Lean_Expr_isConst(v_x_5064_);
if (v___x_5073_ == 0)
{
lean_dec_ref(v_x_5065_);
lean_dec_ref(v_x_5064_);
return v___x_5073_;
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; 
v___x_5074_ = lean_unsigned_to_nat(0u);
v___x_5075_ = lean_array_get_size(v_fnNames_5062_);
v___x_5076_ = lean_nat_dec_lt(v___x_5074_, v___x_5075_);
if (v___x_5076_ == 0)
{
lean_dec_ref(v_x_5065_);
lean_dec_ref(v_x_5064_);
return v___x_5076_;
}
else
{
if (v___x_5076_ == 0)
{
lean_dec_ref(v_x_5065_);
lean_dec_ref(v_x_5064_);
return v___x_5076_;
}
else
{
size_t v___x_5077_; size_t v___x_5078_; uint8_t v___x_5079_; 
v___x_5077_ = ((size_t)0ULL);
v___x_5078_ = lean_usize_of_nat(v___x_5075_);
v___x_5079_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5064_, v_x_5065_, v_numSectionVars_5063_, v_fnNames_5062_, v___x_5077_, v___x_5078_);
lean_dec_ref(v_x_5065_);
lean_dec_ref(v_x_5064_);
return v___x_5079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5080_, lean_object* v_numSectionVars_5081_, lean_object* v_x_5082_, lean_object* v_x_5083_, lean_object* v_x_5084_){
_start:
{
uint8_t v_res_5085_; lean_object* v_r_5086_; 
v_res_5085_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5080_, v_numSectionVars_5081_, v_x_5082_, v_x_5083_, v_x_5084_);
lean_dec(v_numSectionVars_5081_);
lean_dec_ref(v_fnNames_5080_);
v_r_5086_ = lean_box(v_res_5085_);
return v_r_5086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5087_, lean_object* v_fnNames_5088_, lean_object* v_x_5089_, lean_object* v_x_5090_, lean_object* v_x_5091_){
_start:
{
if (lean_obj_tag(v_x_5089_) == 5)
{
lean_object* v_fn_5092_; lean_object* v_arg_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v_fn_5092_ = lean_ctor_get(v_x_5089_, 0);
lean_inc_ref(v_fn_5092_);
v_arg_5093_ = lean_ctor_get(v_x_5089_, 1);
lean_inc_ref(v_arg_5093_);
lean_dec_ref_known(v_x_5089_, 2);
v___x_5094_ = lean_array_set(v_x_5090_, v_x_5091_, v_arg_5093_);
v___x_5095_ = lean_unsigned_to_nat(1u);
v___x_5096_ = lean_nat_sub(v_x_5091_, v___x_5095_);
v___x_5097_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5088_, v_numSectionVars_5087_, v_fn_5092_, v___x_5094_, v___x_5096_);
return v___x_5097_;
}
else
{
uint8_t v___x_5098_; 
v___x_5098_ = l_Lean_Expr_isConst(v_x_5089_);
if (v___x_5098_ == 0)
{
lean_dec_ref(v_x_5090_);
lean_dec_ref(v_x_5089_);
return v___x_5098_;
}
else
{
lean_object* v___x_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; 
v___x_5099_ = lean_unsigned_to_nat(0u);
v___x_5100_ = lean_array_get_size(v_fnNames_5088_);
v___x_5101_ = lean_nat_dec_lt(v___x_5099_, v___x_5100_);
if (v___x_5101_ == 0)
{
lean_dec_ref(v_x_5090_);
lean_dec_ref(v_x_5089_);
return v___x_5101_;
}
else
{
if (v___x_5101_ == 0)
{
lean_dec_ref(v_x_5090_);
lean_dec_ref(v_x_5089_);
return v___x_5101_;
}
else
{
size_t v___x_5102_; size_t v___x_5103_; uint8_t v___x_5104_; 
v___x_5102_ = ((size_t)0ULL);
v___x_5103_ = lean_usize_of_nat(v___x_5100_);
v___x_5104_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5089_, v_x_5090_, v_numSectionVars_5087_, v_fnNames_5088_, v___x_5102_, v___x_5103_);
lean_dec_ref(v_x_5090_);
lean_dec_ref(v_x_5089_);
return v___x_5104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5105_, lean_object* v_fnNames_5106_, lean_object* v_x_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_){
_start:
{
uint8_t v_res_5110_; lean_object* v_r_5111_; 
v_res_5110_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5105_, v_fnNames_5106_, v_x_5107_, v_x_5108_, v_x_5109_);
lean_dec(v_x_5109_);
lean_dec_ref(v_fnNames_5106_);
lean_dec(v_numSectionVars_5105_);
v_r_5111_ = lean_box(v_res_5110_);
return v_r_5111_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5112_, lean_object* v_numSectionVars_5113_, lean_object* v_a_5114_){
_start:
{
lean_object* v_dummy_5115_; lean_object* v_nargs_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; 
v_dummy_5115_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5116_ = l_Lean_Expr_getAppNumArgs(v_a_5114_);
lean_inc(v_nargs_5116_);
v___x_5117_ = lean_mk_array(v_nargs_5116_, v_dummy_5115_);
v___x_5118_ = lean_unsigned_to_nat(1u);
v___x_5119_ = lean_nat_sub(v_nargs_5116_, v___x_5118_);
lean_dec(v_nargs_5116_);
v___x_5120_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5113_, v_fnNames_5112_, v_a_5114_, v___x_5117_, v___x_5119_);
lean_dec(v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5121_, lean_object* v_numSectionVars_5122_, lean_object* v_a_5123_){
_start:
{
uint8_t v_res_5124_; lean_object* v_r_5125_; 
v_res_5124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5121_, v_numSectionVars_5122_, v_a_5123_);
lean_dec(v_numSectionVars_5122_);
lean_dec_ref(v_fnNames_5121_);
v_r_5125_ = lean_box(v_res_5124_);
return v_r_5125_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5126_, lean_object* v_numSectionVars_5127_, lean_object* v_as_5128_, size_t v_i_5129_, size_t v_stop_5130_){
_start:
{
uint8_t v___x_5131_; 
v___x_5131_ = lean_usize_dec_eq(v_i_5129_, v_stop_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = lean_array_uget_borrowed(v_as_5128_, v_i_5129_);
lean_inc(v___x_5132_);
v___x_5133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5126_, v_numSectionVars_5127_, v___x_5132_);
if (v___x_5133_ == 0)
{
size_t v___x_5134_; size_t v___x_5135_; 
v___x_5134_ = ((size_t)1ULL);
v___x_5135_ = lean_usize_add(v_i_5129_, v___x_5134_);
v_i_5129_ = v___x_5135_;
goto _start;
}
else
{
return v___x_5133_;
}
}
else
{
uint8_t v___x_5137_; 
v___x_5137_ = 0;
return v___x_5137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5138_, lean_object* v_numSectionVars_5139_, lean_object* v_as_5140_, lean_object* v_i_5141_, lean_object* v_stop_5142_){
_start:
{
size_t v_i_boxed_5143_; size_t v_stop_boxed_5144_; uint8_t v_res_5145_; lean_object* v_r_5146_; 
v_i_boxed_5143_ = lean_unbox_usize(v_i_5141_);
lean_dec(v_i_5141_);
v_stop_boxed_5144_ = lean_unbox_usize(v_stop_5142_);
lean_dec(v_stop_5142_);
v_res_5145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5138_, v_numSectionVars_5139_, v_as_5140_, v_i_boxed_5143_, v_stop_boxed_5144_);
lean_dec_ref(v_as_5140_);
lean_dec(v_numSectionVars_5139_);
lean_dec_ref(v_fnNames_5138_);
v_r_5146_ = lean_box(v_res_5145_);
return v_r_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5147_, lean_object* v_numSectionVars_5148_, lean_object* v___x_5149_, lean_object* v_x_5150_, lean_object* v_x_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
if (lean_obj_tag(v_x_5150_) == 5)
{
lean_object* v_fn_5158_; lean_object* v_arg_5159_; lean_object* v___x_5160_; 
v_fn_5158_ = lean_ctor_get(v_x_5150_, 0);
lean_inc_ref(v_fn_5158_);
v_arg_5159_ = lean_ctor_get(v_x_5150_, 1);
lean_inc_ref(v_arg_5159_);
lean_dec_ref_known(v_x_5150_, 2);
v___x_5160_ = lean_array_push(v_x_5151_, v_arg_5159_);
v_x_5150_ = v_fn_5158_;
v_x_5151_ = v___x_5160_;
goto _start;
}
else
{
uint8_t v___x_5162_; 
v___x_5162_ = l_Lean_Expr_isConst(v_x_5150_);
if (v___x_5162_ == 0)
{
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v___x_5149_);
goto v___jp_5155_;
}
else
{
lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = lean_unsigned_to_nat(0u);
v___x_5164_ = lean_array_get_size(v_x_5151_);
v___x_5165_ = lean_nat_dec_lt(v___x_5163_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v___x_5149_);
goto v___jp_5155_;
}
else
{
if (v___x_5165_ == 0)
{
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v___x_5149_);
goto v___jp_5155_;
}
else
{
size_t v___x_5166_; size_t v___x_5167_; uint8_t v___x_5168_; 
v___x_5166_ = ((size_t)0ULL);
v___x_5167_ = lean_usize_of_nat(v___x_5164_);
v___x_5168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5147_, v_numSectionVars_5148_, v_x_5151_, v___x_5166_, v___x_5167_);
if (v___x_5168_ == 0)
{
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v___x_5149_);
goto v___jp_5155_;
}
else
{
lean_object* v___x_5169_; uint8_t v___x_5170_; lean_object* v___x_5171_; 
v___x_5169_ = l_Lean_Expr_constName_x21(v_x_5150_);
v___x_5170_ = 0;
v___x_5171_ = l_Lean_Environment_find_x3f(v___x_5149_, v___x_5169_, v___x_5170_);
if (lean_obj_tag(v___x_5171_) == 1)
{
lean_object* v_val_5172_; 
v_val_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_val_5172_);
lean_dec_ref_known(v___x_5171_, 1);
if (lean_obj_tag(v_val_5172_) == 2)
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5198_; 
v___x_5173_ = l_Lean_Expr_constLevels_x21(v_x_5150_);
lean_dec_ref(v_x_5150_);
v___x_5174_ = l_Lean_Core_instantiateValueLevelParams(v_val_5172_, v___x_5173_, v___x_5165_, v___y_5152_, v___y_5153_);
v_isSharedCheck_5198_ = !lean_is_exclusive(v_val_5172_);
if (v_isSharedCheck_5198_ == 0)
{
lean_object* v_unused_5199_; 
v_unused_5199_ = lean_ctor_get(v_val_5172_, 0);
lean_dec(v_unused_5199_);
v___x_5176_ = v_val_5172_;
v_isShared_5177_ = v_isSharedCheck_5198_;
goto v_resetjp_5175_;
}
else
{
lean_dec(v_val_5172_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5198_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5189_; 
v_a_5178_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5180_ = v___x_5174_;
v_isShared_5181_ = v_isSharedCheck_5189_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5174_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5189_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5184_; 
v___x_5182_ = l_Lean_Expr_betaRev(v_a_5178_, v_x_5151_, v___x_5170_, v___x_5170_);
lean_dec_ref(v_x_5151_);
if (v_isShared_5177_ == 0)
{
lean_ctor_set_tag(v___x_5176_, 1);
lean_ctor_set(v___x_5176_, 0, v___x_5182_);
v___x_5184_ = v___x_5176_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5182_);
v___x_5184_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5186_; 
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 0, v___x_5184_);
v___x_5186_ = v___x_5180_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5184_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_del_object(v___x_5176_);
lean_dec_ref(v_x_5151_);
v_a_5190_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5174_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5174_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
else
{
lean_dec(v_val_5172_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
goto v___jp_5155_;
}
}
else
{
lean_dec(v___x_5171_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v_x_5150_);
goto v___jp_5155_;
}
}
}
}
}
}
v___jp_5155_:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5156_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
return v___x_5157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5200_, lean_object* v_numSectionVars_5201_, lean_object* v___x_5202_, lean_object* v_x_5203_, lean_object* v_x_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5200_, v_numSectionVars_5201_, v___x_5202_, v_x_5203_, v_x_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v_numSectionVars_5201_);
lean_dec_ref(v_fnNames_5200_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5209_, lean_object* v_numSectionVars_5210_, lean_object* v_env_5211_, lean_object* v_e_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v___x_5216_ = l_Lean_Expr_getAppNumArgs(v_e_5212_);
v___x_5217_ = lean_mk_empty_array_with_capacity(v___x_5216_);
lean_dec(v___x_5216_);
v___x_5218_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5209_, v_numSectionVars_5210_, v_env_5211_, v_e_5212_, v___x_5217_, v___y_5213_, v___y_5214_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5219_, lean_object* v_numSectionVars_5220_, lean_object* v_env_5221_, lean_object* v_e_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5219_, v_numSectionVars_5220_, v_env_5221_, v_e_5222_, v___y_5223_, v___y_5224_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v_numSectionVars_5220_);
lean_dec_ref(v_fnNames_5219_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5227_, lean_object* v_numSectionVars_5228_, lean_object* v_e_5229_, lean_object* v___f_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v___x_5234_; lean_object* v_env_5235_; lean_object* v___f_5236_; lean_object* v___x_5237_; 
v___x_5234_ = lean_st_ref_get(v___y_5232_);
v_env_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc_ref(v_env_5235_);
lean_dec(v___x_5234_);
v___f_5236_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5236_, 0, v_fnNames_5227_);
lean_closure_set(v___f_5236_, 1, v_numSectionVars_5228_);
lean_closure_set(v___f_5236_, 2, v_env_5235_);
v___x_5237_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5229_, v___f_5236_, v___f_5230_, v___y_5231_, v___y_5232_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5238_, lean_object* v_numSectionVars_5239_, lean_object* v_e_5240_, lean_object* v___f_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5238_, v_numSectionVars_5239_, v_e_5240_, v___f_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5246_, uint8_t v_isExporting_5247_, lean_object* v___x_5248_, lean_object* v_a_x3f_5249_){
_start:
{
lean_object* v___x_5251_; lean_object* v_env_5252_; lean_object* v_nextMacroScope_5253_; lean_object* v_ngen_5254_; lean_object* v_auxDeclNGen_5255_; lean_object* v_traceState_5256_; lean_object* v_recordedDeps_5257_; lean_object* v_messages_5258_; lean_object* v_infoState_5259_; lean_object* v_snapshotTasks_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5271_; 
v___x_5251_ = lean_st_ref_take(v___y_5246_);
v_env_5252_ = lean_ctor_get(v___x_5251_, 0);
v_nextMacroScope_5253_ = lean_ctor_get(v___x_5251_, 1);
v_ngen_5254_ = lean_ctor_get(v___x_5251_, 2);
v_auxDeclNGen_5255_ = lean_ctor_get(v___x_5251_, 3);
v_traceState_5256_ = lean_ctor_get(v___x_5251_, 4);
v_recordedDeps_5257_ = lean_ctor_get(v___x_5251_, 6);
v_messages_5258_ = lean_ctor_get(v___x_5251_, 7);
v_infoState_5259_ = lean_ctor_get(v___x_5251_, 8);
v_snapshotTasks_5260_ = lean_ctor_get(v___x_5251_, 9);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5271_ == 0)
{
lean_object* v_unused_5272_; 
v_unused_5272_ = lean_ctor_get(v___x_5251_, 5);
lean_dec(v_unused_5272_);
v___x_5262_ = v___x_5251_;
v_isShared_5263_ = v_isSharedCheck_5271_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_snapshotTasks_5260_);
lean_inc(v_infoState_5259_);
lean_inc(v_messages_5258_);
lean_inc(v_recordedDeps_5257_);
lean_inc(v_traceState_5256_);
lean_inc(v_auxDeclNGen_5255_);
lean_inc(v_ngen_5254_);
lean_inc(v_nextMacroScope_5253_);
lean_inc(v_env_5252_);
lean_dec(v___x_5251_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5271_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5267_; 
v___x_5264_ = lean_box(0);
v___x_5265_ = l_Lean_Environment_setExporting(v_env_5252_, v_isExporting_5247_);
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 5, v___x_5248_);
lean_ctor_set(v___x_5262_, 0, v___x_5265_);
v___x_5267_ = v___x_5262_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5270_, 1, v_nextMacroScope_5253_);
lean_ctor_set(v_reuseFailAlloc_5270_, 2, v_ngen_5254_);
lean_ctor_set(v_reuseFailAlloc_5270_, 3, v_auxDeclNGen_5255_);
lean_ctor_set(v_reuseFailAlloc_5270_, 4, v_traceState_5256_);
lean_ctor_set(v_reuseFailAlloc_5270_, 5, v___x_5248_);
lean_ctor_set(v_reuseFailAlloc_5270_, 6, v_recordedDeps_5257_);
lean_ctor_set(v_reuseFailAlloc_5270_, 7, v_messages_5258_);
lean_ctor_set(v_reuseFailAlloc_5270_, 8, v_infoState_5259_);
lean_ctor_set(v_reuseFailAlloc_5270_, 9, v_snapshotTasks_5260_);
v___x_5267_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5268_ = lean_st_ref_put(v___y_5246_, v___x_5267_);
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5264_);
return v___x_5269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5273_, lean_object* v_isExporting_5274_, lean_object* v___x_5275_, lean_object* v_a_x3f_5276_, lean_object* v___y_5277_){
_start:
{
uint8_t v_isExporting_boxed_5278_; lean_object* v_res_5279_; 
v_isExporting_boxed_5278_ = lean_unbox(v_isExporting_5274_);
v_res_5279_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5273_, v_isExporting_boxed_5278_, v___x_5275_, v_a_x3f_5276_);
lean_dec(v_a_x3f_5276_);
lean_dec(v___y_5273_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5280_, uint8_t v_isExporting_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; lean_object* v_env_5286_; lean_object* v___x_5287_; uint8_t v_isModule_5288_; 
v___x_5285_ = lean_st_ref_get(v___y_5283_);
v_env_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc_ref(v_env_5286_);
lean_dec(v___x_5285_);
v___x_5287_ = l_Lean_Environment_header(v_env_5286_);
v_isModule_5288_ = lean_ctor_get_uint8(v___x_5287_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5287_);
if (v_isModule_5288_ == 0)
{
lean_object* v___x_5289_; 
lean_dec_ref(v_env_5286_);
lean_inc(v___y_5283_);
lean_inc_ref(v___y_5282_);
v___x_5289_ = lean_apply_3(v_x_5280_, v___y_5282_, v___y_5283_, lean_box(0));
return v___x_5289_;
}
else
{
uint8_t v_isExporting_5290_; 
v_isExporting_5290_ = lean_ctor_get_uint8(v_env_5286_, sizeof(void*)*13);
lean_dec_ref(v_env_5286_);
if (v_isExporting_5281_ == 0)
{
if (v_isExporting_5290_ == 0)
{
lean_object* v___x_5342_; 
lean_inc(v___y_5283_);
lean_inc_ref(v___y_5282_);
v___x_5342_ = lean_apply_3(v_x_5280_, v___y_5282_, v___y_5283_, lean_box(0));
return v___x_5342_;
}
else
{
goto v___jp_5291_;
}
}
else
{
if (v_isExporting_5290_ == 0)
{
goto v___jp_5291_;
}
else
{
lean_object* v___x_5343_; 
lean_inc(v___y_5283_);
lean_inc_ref(v___y_5282_);
v___x_5343_ = lean_apply_3(v_x_5280_, v___y_5282_, v___y_5283_, lean_box(0));
return v___x_5343_;
}
}
v___jp_5291_:
{
lean_object* v___x_5292_; lean_object* v_env_5293_; lean_object* v_nextMacroScope_5294_; lean_object* v_ngen_5295_; lean_object* v_auxDeclNGen_5296_; lean_object* v_traceState_5297_; lean_object* v_recordedDeps_5298_; lean_object* v_messages_5299_; lean_object* v_infoState_5300_; lean_object* v_snapshotTasks_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5340_; 
v___x_5292_ = lean_st_ref_take(v___y_5283_);
v_env_5293_ = lean_ctor_get(v___x_5292_, 0);
v_nextMacroScope_5294_ = lean_ctor_get(v___x_5292_, 1);
v_ngen_5295_ = lean_ctor_get(v___x_5292_, 2);
v_auxDeclNGen_5296_ = lean_ctor_get(v___x_5292_, 3);
v_traceState_5297_ = lean_ctor_get(v___x_5292_, 4);
v_recordedDeps_5298_ = lean_ctor_get(v___x_5292_, 6);
v_messages_5299_ = lean_ctor_get(v___x_5292_, 7);
v_infoState_5300_ = lean_ctor_get(v___x_5292_, 8);
v_snapshotTasks_5301_ = lean_ctor_get(v___x_5292_, 9);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5340_ == 0)
{
lean_object* v_unused_5341_; 
v_unused_5341_ = lean_ctor_get(v___x_5292_, 5);
lean_dec(v_unused_5341_);
v___x_5303_ = v___x_5292_;
v_isShared_5304_ = v_isSharedCheck_5340_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_snapshotTasks_5301_);
lean_inc(v_infoState_5300_);
lean_inc(v_messages_5299_);
lean_inc(v_recordedDeps_5298_);
lean_inc(v_traceState_5297_);
lean_inc(v_auxDeclNGen_5296_);
lean_inc(v_ngen_5295_);
lean_inc(v_nextMacroScope_5294_);
lean_inc(v_env_5293_);
lean_dec(v___x_5292_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5340_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5308_; 
v___x_5305_ = l_Lean_Environment_setExporting(v_env_5293_, v_isExporting_5281_);
v___x_5306_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 5, v___x_5306_);
lean_ctor_set(v___x_5303_, 0, v___x_5305_);
v___x_5308_ = v___x_5303_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5305_);
lean_ctor_set(v_reuseFailAlloc_5339_, 1, v_nextMacroScope_5294_);
lean_ctor_set(v_reuseFailAlloc_5339_, 2, v_ngen_5295_);
lean_ctor_set(v_reuseFailAlloc_5339_, 3, v_auxDeclNGen_5296_);
lean_ctor_set(v_reuseFailAlloc_5339_, 4, v_traceState_5297_);
lean_ctor_set(v_reuseFailAlloc_5339_, 5, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5339_, 6, v_recordedDeps_5298_);
lean_ctor_set(v_reuseFailAlloc_5339_, 7, v_messages_5299_);
lean_ctor_set(v_reuseFailAlloc_5339_, 8, v_infoState_5300_);
lean_ctor_set(v_reuseFailAlloc_5339_, 9, v_snapshotTasks_5301_);
v___x_5308_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
lean_object* v___x_5309_; lean_object* v_r_5310_; 
v___x_5309_ = lean_st_ref_put(v___y_5283_, v___x_5308_);
lean_inc(v___y_5283_);
lean_inc_ref(v___y_5282_);
v_r_5310_ = lean_apply_3(v_x_5280_, v___y_5282_, v___y_5283_, lean_box(0));
if (lean_obj_tag(v_r_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5327_; 
v_a_5311_ = lean_ctor_get(v_r_5310_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v_r_5310_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5313_ = v_r_5310_;
v_isShared_5314_ = v_isSharedCheck_5327_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v_r_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5327_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
lean_inc(v_a_5311_);
if (v_isShared_5314_ == 0)
{
lean_ctor_set_tag(v___x_5313_, 1);
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5311_);
v___x_5316_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5324_; 
v___x_5317_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5283_, v_isExporting_5290_, v___x_5306_, v___x_5316_);
lean_dec_ref(v___x_5316_);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5324_ == 0)
{
lean_object* v_unused_5325_; 
v_unused_5325_ = lean_ctor_get(v___x_5317_, 0);
lean_dec(v_unused_5325_);
v___x_5319_ = v___x_5317_;
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
else
{
lean_dec(v___x_5317_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5322_; 
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v_a_5311_);
v___x_5322_ = v___x_5319_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5311_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v_a_5328_ = lean_ctor_get(v_r_5310_, 0);
lean_inc(v_a_5328_);
lean_dec_ref_known(v_r_5310_, 1);
v___x_5329_ = lean_box(0);
v___x_5330_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5283_, v_isExporting_5290_, v___x_5306_, v___x_5329_);
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
lean_ctor_set_tag(v___x_5332_, 1);
lean_ctor_set(v___x_5332_, 0, v_a_5328_);
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5328_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5344_, lean_object* v_isExporting_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
uint8_t v_isExporting_boxed_5349_; lean_object* v_res_5350_; 
v_isExporting_boxed_5349_ = lean_unbox(v_isExporting_5345_);
v_res_5350_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5344_, v_isExporting_boxed_5349_, v___y_5346_, v___y_5347_);
lean_dec(v___y_5347_);
lean_dec_ref(v___y_5346_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5351_, uint8_t v_when_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
if (v_when_5352_ == 0)
{
lean_object* v___x_5356_; 
lean_inc(v___y_5354_);
lean_inc_ref(v___y_5353_);
v___x_5356_ = lean_apply_3(v_x_5351_, v___y_5353_, v___y_5354_, lean_box(0));
return v___x_5356_;
}
else
{
uint8_t v___x_5357_; lean_object* v___x_5358_; 
v___x_5357_ = 0;
v___x_5358_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5351_, v___x_5357_, v___y_5353_, v___y_5354_);
return v___x_5358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5359_, lean_object* v_when_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
uint8_t v_when_boxed_5364_; lean_object* v_res_5365_; 
v_when_boxed_5364_ = lean_unbox(v_when_5360_);
v_res_5365_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5359_, v_when_boxed_5364_, v___y_5361_, v___y_5362_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5366_, lean_object* v_numSectionVars_5367_, lean_object* v_e_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v___f_5372_; lean_object* v___f_5373_; uint8_t v___x_5374_; lean_object* v___x_5375_; 
v___f_5372_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5373_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5373_, 0, v_fnNames_5366_);
lean_closure_set(v___f_5373_, 1, v_numSectionVars_5367_);
lean_closure_set(v___f_5373_, 2, v_e_5368_);
lean_closure_set(v___f_5373_, 3, v___f_5372_);
v___x_5374_ = 1;
v___x_5375_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5373_, v___x_5374_, v_a_5369_, v_a_5370_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5376_, lean_object* v_numSectionVars_5377_, lean_object* v_e_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5376_, v_numSectionVars_5377_, v_e_5378_, v_a_5379_, v_a_5380_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5383_, lean_object* v_x_5384_, uint8_t v_isExporting_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5384_, v_isExporting_5385_, v___y_5386_, v___y_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5390_, lean_object* v_x_5391_, lean_object* v_isExporting_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
uint8_t v_isExporting_boxed_5396_; lean_object* v_res_5397_; 
v_isExporting_boxed_5396_ = lean_unbox(v_isExporting_5392_);
v_res_5397_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5390_, v_x_5391_, v_isExporting_boxed_5396_, v___y_5393_, v___y_5394_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5398_, lean_object* v_x_5399_, uint8_t v_when_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5399_, v_when_5400_, v___y_5401_, v___y_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5405_, lean_object* v_x_5406_, lean_object* v_when_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
uint8_t v_when_boxed_5411_; lean_object* v_res_5412_; 
v_when_boxed_5411_ = lean_unbox(v_when_5407_);
v_res_5412_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5405_, v_x_5406_, v_when_boxed_5411_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5417_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5418_, 0, v___x_5417_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec_ref(v_x_5419_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v___y_5429_; lean_object* v___x_5432_; 
v___x_5432_ = l_Lean_inaccessible_x3f(v_e_5424_);
if (lean_obj_tag(v___x_5432_) == 1)
{
lean_object* v_val_5433_; 
lean_dec_ref(v_e_5424_);
v_val_5433_ = lean_ctor_get(v___x_5432_, 0);
lean_inc(v_val_5433_);
lean_dec_ref_known(v___x_5432_, 1);
v___y_5429_ = v_val_5433_;
goto v___jp_5428_;
}
else
{
lean_dec(v___x_5432_);
v___y_5429_ = v_e_5424_;
goto v___jp_5428_;
}
v___jp_5428_:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5430_, 0, v___y_5429_);
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
return v___x_5431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v___f_5445_; lean_object* v___f_5446_; lean_object* v___x_5447_; 
v___f_5445_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5446_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5447_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5441_, v___f_5445_, v___f_5446_, v_a_5442_, v_a_5443_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5448_, v_a_5449_, v_a_5450_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v___y_5458_; lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_patternWithRef_x3f(v_e_5453_);
if (lean_obj_tag(v___x_5461_) == 1)
{
lean_object* v_val_5462_; lean_object* v_snd_5463_; 
lean_dec_ref(v_e_5453_);
v_val_5462_ = lean_ctor_get(v___x_5461_, 0);
lean_inc(v_val_5462_);
lean_dec_ref_known(v___x_5461_, 1);
v_snd_5463_ = lean_ctor_get(v_val_5462_, 1);
lean_inc(v_snd_5463_);
lean_dec(v_val_5462_);
v___y_5458_ = v_snd_5463_;
goto v___jp_5457_;
}
else
{
lean_dec(v___x_5461_);
v___y_5458_ = v_e_5453_;
goto v___jp_5457_;
}
v___jp_5457_:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5459_, 0, v___y_5458_);
v___x_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5460_, 0, v___x_5459_);
return v___x_5460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5464_, v___y_5465_, v___y_5466_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_){
_start:
{
lean_object* v___f_5474_; lean_object* v___f_5475_; lean_object* v___x_5476_; 
v___f_5474_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5475_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5476_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5470_, v___f_5474_, v___f_5475_, v_a_5471_, v_a_5472_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5477_, v_a_5478_, v_a_5479_);
lean_dec(v_a_5479_);
lean_dec_ref(v_a_5478_);
return v_res_5481_;
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
