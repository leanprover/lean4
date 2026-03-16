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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_7_);
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
lean_dec_ref(v_x_65_);
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
lean_dec_ref(v_x_99_);
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
lean_dec_ref(v_x_99_);
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
lean_dec_ref(v_x_99_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object* v_toApplicative_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_e_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_toPure_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toPure_182_ = lean_ctor_get(v_toApplicative_177_, 1);
lean_inc(v_toPure_182_);
lean_dec_ref(v_toApplicative_177_);
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_178_, v___x_179_, v_a_181_, v_e_180_);
v___x_184_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_e_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(v_toApplicative_185_, v___x_186_, v___x_187_, v_e_188_, v_a_189_);
lean_dec_ref(v_a_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_pre_191_, lean_object* v_e_192_, lean_object* v_inst_193_, lean_object* v___f_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v_a_197_, lean_object* v_toBind_198_, lean_object* v___f_199_, lean_object* v_toApplicative_200_, lean_object* v_a_201_){
_start:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_2298__overap_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v_toApplicative_200_);
v___x_202_ = lean_apply_1(v_pre_191_, v_e_192_);
v___x_203_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_203_, 0, lean_box(0));
lean_closure_set(v___x_203_, 1, lean_box(0));
lean_closure_set(v___x_203_, 2, lean_box(0));
lean_closure_set(v___x_203_, 3, lean_box(0));
lean_closure_set(v___x_203_, 4, v___x_202_);
v___x_204_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_204_, 0, lean_box(0));
lean_closure_set(v___x_204_, 1, lean_box(0));
lean_closure_set(v___x_204_, 2, v_inst_193_);
lean_closure_set(v___x_204_, 3, lean_box(0));
lean_closure_set(v___x_204_, 4, lean_box(0));
lean_closure_set(v___x_204_, 5, v___x_203_);
lean_closure_set(v___x_204_, 6, v___f_194_);
v___x_2298__overap_205_ = l_Lean_Core_withIncRecDepth___redArg(v___x_195_, v___x_196_, v___x_204_);
v___x_206_ = lean_apply_1(v___x_2298__overap_205_, v_a_197_);
v___x_207_ = lean_apply_4(v_toBind_198_, lean_box(0), lean_box(0), v___x_206_, v___f_199_);
return v___x_207_;
}
else
{
lean_object* v_val_208_; lean_object* v_toPure_209_; lean_object* v___x_210_; 
lean_dec(v___f_199_);
lean_dec(v_toBind_198_);
lean_dec(v_a_197_);
lean_dec_ref(v___x_196_);
lean_dec_ref(v___x_195_);
lean_dec(v___f_194_);
lean_dec_ref(v_inst_193_);
lean_dec_ref(v_e_192_);
lean_dec(v_pre_191_);
v_val_208_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_val_208_);
lean_dec_ref(v_a_201_);
v_toPure_209_ = lean_ctor_get(v_toApplicative_200_, 1);
lean_inc(v_toPure_209_);
lean_dec_ref(v_toApplicative_200_);
v___x_210_ = lean_apply_2(v_toPure_209_, lean_box(0), v_val_208_);
return v___x_210_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_instMonadControlReaderT(lean_box(0), lean_box(0));
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_a_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_pre_217_, lean_object* v_post_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v___y_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l_Lean_mkAppN(v_a_214_, v_a_222_);
v___x_224_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_215_, v_inst_216_, v_pre_217_, v_post_218_, v_x_219_, v_x_220_, v___x_223_, v___y_221_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_a_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_pre_228_, lean_object* v_post_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_a_225_, v_inst_226_, v_inst_227_, v_pre_228_, v_post_229_, v_x_230_, v_x_231_, v___y_232_, v_a_233_);
lean_dec_ref(v_a_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_pre_237_, lean_object* v_post_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v_args_242_, lean_object* v___x_243_, lean_object* v_toBind_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___f_246_; lean_object* v___x_247_; size_t v_sz_248_; size_t v___x_249_; lean_object* v___x_2056__overap_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc(v___y_241_);
lean_inc(v_x_240_);
lean_inc(v_post_238_);
lean_inc(v_pre_237_);
lean_inc_ref(v_inst_236_);
lean_inc_ref(v_inst_235_);
v___f_246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_246_, 0, v_a_245_);
lean_closure_set(v___f_246_, 1, v_inst_235_);
lean_closure_set(v___f_246_, 2, v_inst_236_);
lean_closure_set(v___f_246_, 3, v_pre_237_);
lean_closure_set(v___f_246_, 4, v_post_238_);
lean_closure_set(v___f_246_, 5, v_x_239_);
lean_closure_set(v___f_246_, 6, v_x_240_);
lean_closure_set(v___f_246_, 7, v___y_241_);
v___x_247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg), 8, 6);
lean_closure_set(v___x_247_, 0, v_inst_235_);
lean_closure_set(v___x_247_, 1, v_inst_236_);
lean_closure_set(v___x_247_, 2, v_pre_237_);
lean_closure_set(v___x_247_, 3, v_post_238_);
lean_closure_set(v___x_247_, 4, v_x_239_);
lean_closure_set(v___x_247_, 5, v_x_240_);
v_sz_248_ = lean_array_size(v_args_242_);
v___x_249_ = ((size_t)0ULL);
v___x_2056__overap_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_243_, v___x_247_, v_sz_248_, v___x_249_, v_args_242_);
v___x_251_ = lean_apply_1(v___x_2056__overap_250_, v___y_241_);
v___x_252_ = lean_apply_4(v_toBind_244_, lean_box(0), lean_box(0), v___x_251_, v___f_246_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_pre_255_, lean_object* v_post_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v___x_259_, lean_object* v_toBind_260_, lean_object* v_f_261_, lean_object* v_args_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_inc(v_toBind_260_);
lean_inc(v___y_263_);
lean_inc(v_x_258_);
lean_inc(v_post_256_);
lean_inc(v_pre_255_);
lean_inc_ref(v_inst_254_);
lean_inc_ref(v_inst_253_);
v___f_264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5), 11, 10);
lean_closure_set(v___f_264_, 0, v_inst_253_);
lean_closure_set(v___f_264_, 1, v_inst_254_);
lean_closure_set(v___f_264_, 2, v_pre_255_);
lean_closure_set(v___f_264_, 3, v_post_256_);
lean_closure_set(v___f_264_, 4, v_x_257_);
lean_closure_set(v___f_264_, 5, v_x_258_);
lean_closure_set(v___f_264_, 6, v___y_263_);
lean_closure_set(v___f_264_, 7, v_args_262_);
lean_closure_set(v___f_264_, 8, v___x_259_);
lean_closure_set(v___f_264_, 9, v_toBind_260_);
v___x_265_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_253_, v_inst_254_, v_pre_255_, v_post_256_, v_x_257_, v_x_258_, v_f_261_, v___y_263_);
v___x_266_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_265_, v___f_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderName_267_, lean_object* v_a_268_, uint8_t v_binderInfo_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_pre_272_, lean_object* v_post_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v_binderType_278_, lean_object* v_body_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___y_282_; size_t v___x_289_; size_t v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_ptr_addr(v_binderType_278_);
v___x_290_ = lean_ptr_addr(v_a_268_);
v___x_291_ = lean_usize_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
v___y_282_ = v___x_291_;
goto v___jp_281_;
}
else
{
size_t v___x_292_; size_t v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_ptr_addr(v_body_279_);
v___x_293_ = lean_ptr_addr(v_a_280_);
v___x_294_ = lean_usize_dec_eq(v___x_292_, v___x_293_);
v___y_282_ = v___x_294_;
goto v___jp_281_;
}
v___jp_281_:
{
if (v___y_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___y_277_);
v___x_283_ = l_Lean_Expr_forallE___override(v_binderName_267_, v_a_268_, v_a_280_, v_binderInfo_269_);
v___x_284_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_270_, v_inst_271_, v_pre_272_, v_post_273_, v_x_274_, v_x_275_, v___x_283_, v___y_276_);
return v___x_284_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_269_, v_binderInfo_269_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v___y_277_);
v___x_286_ = l_Lean_Expr_forallE___override(v_binderName_267_, v_a_268_, v_a_280_, v_binderInfo_269_);
v___x_287_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_270_, v_inst_271_, v_pre_272_, v_post_273_, v_x_274_, v_x_275_, v___x_286_, v___y_276_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; 
lean_dec_ref(v_a_280_);
lean_dec_ref(v_a_268_);
lean_dec(v_binderName_267_);
v___x_288_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_270_, v_inst_271_, v_pre_272_, v_post_273_, v_x_274_, v_x_275_, v___y_277_, v___y_276_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderName_295_, lean_object* v_a_296_, lean_object* v_binderInfo_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_pre_300_, lean_object* v_post_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v_binderType_306_, lean_object* v_body_307_, lean_object* v_a_308_){
_start:
{
uint8_t v_binderInfo_2573__boxed_309_; lean_object* v_res_310_; 
v_binderInfo_2573__boxed_309_ = lean_unbox(v_binderInfo_297_);
v_res_310_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderName_295_, v_a_296_, v_binderInfo_2573__boxed_309_, v_inst_298_, v_inst_299_, v_pre_300_, v_post_301_, v_x_302_, v_x_303_, v___y_304_, v___y_305_, v_binderType_306_, v_body_307_, v_a_308_);
lean_dec_ref(v_body_307_);
lean_dec_ref(v_binderType_306_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderName_311_, uint8_t v_binderInfo_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_pre_315_, lean_object* v_post_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v_binderType_321_, lean_object* v_body_322_, lean_object* v_toBind_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_box(v_binderInfo_312_);
lean_inc_ref(v_body_322_);
lean_inc(v___y_319_);
lean_inc(v_x_318_);
lean_inc(v_post_316_);
lean_inc(v_pre_315_);
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___f_326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 14, 13);
lean_closure_set(v___f_326_, 0, v_binderName_311_);
lean_closure_set(v___f_326_, 1, v_a_324_);
lean_closure_set(v___f_326_, 2, v___x_325_);
lean_closure_set(v___f_326_, 3, v_inst_313_);
lean_closure_set(v___f_326_, 4, v_inst_314_);
lean_closure_set(v___f_326_, 5, v_pre_315_);
lean_closure_set(v___f_326_, 6, v_post_316_);
lean_closure_set(v___f_326_, 7, v_x_317_);
lean_closure_set(v___f_326_, 8, v_x_318_);
lean_closure_set(v___f_326_, 9, v___y_319_);
lean_closure_set(v___f_326_, 10, v___y_320_);
lean_closure_set(v___f_326_, 11, v_binderType_321_);
lean_closure_set(v___f_326_, 12, v_body_322_);
v___x_327_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_313_, v_inst_314_, v_pre_315_, v_post_316_, v_x_317_, v_x_318_, v_body_322_, v___y_319_);
v___x_328_ = lean_apply_4(v_toBind_323_, lean_box(0), lean_box(0), v___x_327_, v___f_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderName_329_, lean_object* v_binderInfo_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_pre_333_, lean_object* v_post_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v_binderType_339_, lean_object* v_body_340_, lean_object* v_toBind_341_, lean_object* v_a_342_){
_start:
{
uint8_t v_binderInfo_2450__boxed_343_; lean_object* v_res_344_; 
v_binderInfo_2450__boxed_343_ = lean_unbox(v_binderInfo_330_);
v_res_344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderName_329_, v_binderInfo_2450__boxed_343_, v_inst_331_, v_inst_332_, v_pre_333_, v_post_334_, v_x_335_, v_x_336_, v___y_337_, v___y_338_, v_binderType_339_, v_body_340_, v_toBind_341_, v_a_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderName_345_, lean_object* v_a_346_, uint8_t v_binderInfo_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_pre_350_, lean_object* v_post_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v_binderType_356_, lean_object* v_body_357_, lean_object* v_a_358_){
_start:
{
uint8_t v___y_360_; size_t v___x_367_; size_t v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_ptr_addr(v_binderType_356_);
v___x_368_ = lean_ptr_addr(v_a_346_);
v___x_369_ = lean_usize_dec_eq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
v___y_360_ = v___x_369_;
goto v___jp_359_;
}
else
{
size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_ptr_addr(v_body_357_);
v___x_371_ = lean_ptr_addr(v_a_358_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
v___y_360_ = v___x_372_;
goto v___jp_359_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v___y_355_);
v___x_361_ = l_Lean_Expr_lam___override(v_binderName_345_, v_a_346_, v_a_358_, v_binderInfo_347_);
v___x_362_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___x_361_, v___y_354_);
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_347_, v_binderInfo_347_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v___y_355_);
v___x_364_ = l_Lean_Expr_lam___override(v_binderName_345_, v_a_346_, v_a_358_, v_binderInfo_347_);
v___x_365_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___x_364_, v___y_354_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec_ref(v_a_358_);
lean_dec_ref(v_a_346_);
lean_dec(v_binderName_345_);
v___x_366_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___y_355_, v___y_354_);
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderName_373_, lean_object* v_a_374_, lean_object* v_binderInfo_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_pre_378_, lean_object* v_post_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v_binderType_384_, lean_object* v_body_385_, lean_object* v_a_386_){
_start:
{
uint8_t v_binderInfo_2549__boxed_387_; lean_object* v_res_388_; 
v_binderInfo_2549__boxed_387_ = lean_unbox(v_binderInfo_375_);
v_res_388_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderName_373_, v_a_374_, v_binderInfo_2549__boxed_387_, v_inst_376_, v_inst_377_, v_pre_378_, v_post_379_, v_x_380_, v_x_381_, v___y_382_, v___y_383_, v_binderType_384_, v_body_385_, v_a_386_);
lean_dec_ref(v_body_385_);
lean_dec_ref(v_binderType_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderName_389_, uint8_t v_binderInfo_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_pre_393_, lean_object* v_post_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v_binderType_399_, lean_object* v_body_400_, lean_object* v_toBind_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_box(v_binderInfo_390_);
lean_inc_ref(v_body_400_);
lean_inc(v___y_397_);
lean_inc(v_x_396_);
lean_inc(v_post_394_);
lean_inc(v_pre_393_);
lean_inc_ref(v_inst_392_);
lean_inc_ref(v_inst_391_);
v___f_404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 14, 13);
lean_closure_set(v___f_404_, 0, v_binderName_389_);
lean_closure_set(v___f_404_, 1, v_a_402_);
lean_closure_set(v___f_404_, 2, v___x_403_);
lean_closure_set(v___f_404_, 3, v_inst_391_);
lean_closure_set(v___f_404_, 4, v_inst_392_);
lean_closure_set(v___f_404_, 5, v_pre_393_);
lean_closure_set(v___f_404_, 6, v_post_394_);
lean_closure_set(v___f_404_, 7, v_x_395_);
lean_closure_set(v___f_404_, 8, v_x_396_);
lean_closure_set(v___f_404_, 9, v___y_397_);
lean_closure_set(v___f_404_, 10, v___y_398_);
lean_closure_set(v___f_404_, 11, v_binderType_399_);
lean_closure_set(v___f_404_, 12, v_body_400_);
v___x_405_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_391_, v_inst_392_, v_pre_393_, v_post_394_, v_x_395_, v_x_396_, v_body_400_, v___y_397_);
v___x_406_ = lean_apply_4(v_toBind_401_, lean_box(0), lean_box(0), v___x_405_, v___f_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderName_407_, lean_object* v_binderInfo_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_pre_411_, lean_object* v_post_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v_binderType_417_, lean_object* v_body_418_, lean_object* v_toBind_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_binderInfo_2400__boxed_421_; lean_object* v_res_422_; 
v_binderInfo_2400__boxed_421_ = lean_unbox(v_binderInfo_408_);
v_res_422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderName_407_, v_binderInfo_2400__boxed_421_, v_inst_409_, v_inst_410_, v_pre_411_, v_post_412_, v_x_413_, v_x_414_, v___y_415_, v___y_416_, v_binderType_417_, v_body_418_, v_toBind_419_, v_a_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_declName_423_, lean_object* v_a_424_, lean_object* v_a_425_, uint8_t v_nondep_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_pre_429_, lean_object* v_post_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v_body_434_, lean_object* v___y_435_, lean_object* v_type_436_, lean_object* v_value_437_, lean_object* v_a_438_){
_start:
{
uint8_t v___y_440_; size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_type_436_);
v___x_450_ = lean_ptr_addr(v_a_424_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
v___y_440_ = v___x_451_;
goto v___jp_439_;
}
else
{
size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_ptr_addr(v_value_437_);
v___x_453_ = lean_ptr_addr(v_a_425_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
v___y_440_ = v___x_454_;
goto v___jp_439_;
}
v___jp_439_:
{
if (v___y_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v___y_435_);
v___x_441_ = l_Lean_Expr_letE___override(v_declName_423_, v_a_424_, v_a_425_, v_a_438_, v_nondep_426_);
v___x_442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_427_, v_inst_428_, v_pre_429_, v_post_430_, v_x_431_, v_x_432_, v___x_441_, v___y_433_);
return v___x_442_;
}
else
{
size_t v___x_443_; size_t v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_ptr_addr(v_body_434_);
v___x_444_ = lean_ptr_addr(v_a_438_);
v___x_445_ = lean_usize_dec_eq(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref(v___y_435_);
v___x_446_ = l_Lean_Expr_letE___override(v_declName_423_, v_a_424_, v_a_425_, v_a_438_, v_nondep_426_);
v___x_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_427_, v_inst_428_, v_pre_429_, v_post_430_, v_x_431_, v_x_432_, v___x_446_, v___y_433_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
lean_dec_ref(v_a_438_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_declName_423_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_427_, v_inst_428_, v_pre_429_, v_post_430_, v_x_431_, v_x_432_, v___y_435_, v___y_433_);
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object* v_declName_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_nondep_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_pre_461_, lean_object* v_post_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v_body_466_, lean_object* v___y_467_, lean_object* v_type_468_, lean_object* v_value_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_nondep_2597__boxed_471_; lean_object* v_res_472_; 
v_nondep_2597__boxed_471_ = lean_unbox(v_nondep_458_);
v_res_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_declName_455_, v_a_456_, v_a_457_, v_nondep_2597__boxed_471_, v_inst_459_, v_inst_460_, v_pre_461_, v_post_462_, v_x_463_, v_x_464_, v___y_465_, v_body_466_, v___y_467_, v_type_468_, v_value_469_, v_a_470_);
lean_dec_ref(v_value_469_);
lean_dec_ref(v_type_468_);
lean_dec_ref(v_body_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_declName_473_, lean_object* v_a_474_, uint8_t v_nondep_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_pre_478_, lean_object* v_post_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v_body_483_, lean_object* v___y_484_, lean_object* v_type_485_, lean_object* v_value_486_, lean_object* v_toBind_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_box(v_nondep_475_);
lean_inc_ref(v_body_483_);
lean_inc(v___y_482_);
lean_inc(v_x_481_);
lean_inc(v_post_479_);
lean_inc(v_pre_478_);
lean_inc_ref(v_inst_477_);
lean_inc_ref(v_inst_476_);
v___f_490_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 16, 15);
lean_closure_set(v___f_490_, 0, v_declName_473_);
lean_closure_set(v___f_490_, 1, v_a_474_);
lean_closure_set(v___f_490_, 2, v_a_488_);
lean_closure_set(v___f_490_, 3, v___x_489_);
lean_closure_set(v___f_490_, 4, v_inst_476_);
lean_closure_set(v___f_490_, 5, v_inst_477_);
lean_closure_set(v___f_490_, 6, v_pre_478_);
lean_closure_set(v___f_490_, 7, v_post_479_);
lean_closure_set(v___f_490_, 8, v_x_480_);
lean_closure_set(v___f_490_, 9, v_x_481_);
lean_closure_set(v___f_490_, 10, v___y_482_);
lean_closure_set(v___f_490_, 11, v_body_483_);
lean_closure_set(v___f_490_, 12, v___y_484_);
lean_closure_set(v___f_490_, 13, v_type_485_);
lean_closure_set(v___f_490_, 14, v_value_486_);
v___x_491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_476_, v_inst_477_, v_pre_478_, v_post_479_, v_x_480_, v_x_481_, v_body_483_, v___y_482_);
v___x_492_ = lean_apply_4(v_toBind_487_, lean_box(0), lean_box(0), v___x_491_, v___f_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object* v_declName_493_, lean_object* v_a_494_, lean_object* v_nondep_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_pre_498_, lean_object* v_post_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v_body_503_, lean_object* v___y_504_, lean_object* v_type_505_, lean_object* v_value_506_, lean_object* v_toBind_507_, lean_object* v_a_508_){
_start:
{
uint8_t v_nondep_2413__boxed_509_; lean_object* v_res_510_; 
v_nondep_2413__boxed_509_ = lean_unbox(v_nondep_495_);
v_res_510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_declName_493_, v_a_494_, v_nondep_2413__boxed_509_, v_inst_496_, v_inst_497_, v_pre_498_, v_post_499_, v_x_500_, v_x_501_, v___y_502_, v_body_503_, v___y_504_, v_type_505_, v_value_506_, v_toBind_507_, v_a_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_declName_511_, uint8_t v_nondep_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_pre_515_, lean_object* v_post_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v_body_520_, lean_object* v___y_521_, lean_object* v_type_522_, lean_object* v_value_523_, lean_object* v_toBind_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(v_nondep_512_);
lean_inc(v_toBind_524_);
lean_inc_ref(v_value_523_);
lean_inc(v___y_519_);
lean_inc(v_x_518_);
lean_inc(v_post_516_);
lean_inc(v_pre_515_);
lean_inc_ref(v_inst_514_);
lean_inc_ref(v_inst_513_);
v___f_527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_527_, 0, v_declName_511_);
lean_closure_set(v___f_527_, 1, v_a_525_);
lean_closure_set(v___f_527_, 2, v___x_526_);
lean_closure_set(v___f_527_, 3, v_inst_513_);
lean_closure_set(v___f_527_, 4, v_inst_514_);
lean_closure_set(v___f_527_, 5, v_pre_515_);
lean_closure_set(v___f_527_, 6, v_post_516_);
lean_closure_set(v___f_527_, 7, v_x_517_);
lean_closure_set(v___f_527_, 8, v_x_518_);
lean_closure_set(v___f_527_, 9, v___y_519_);
lean_closure_set(v___f_527_, 10, v_body_520_);
lean_closure_set(v___f_527_, 11, v___y_521_);
lean_closure_set(v___f_527_, 12, v_type_522_);
lean_closure_set(v___f_527_, 13, v_value_523_);
lean_closure_set(v___f_527_, 14, v_toBind_524_);
v___x_528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_513_, v_inst_514_, v_pre_515_, v_post_516_, v_x_517_, v_x_518_, v_value_523_, v___y_519_);
v___x_529_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_528_, v___f_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_declName_530_, lean_object* v_nondep_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_pre_534_, lean_object* v_post_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v_body_539_, lean_object* v___y_540_, lean_object* v_type_541_, lean_object* v_value_542_, lean_object* v_toBind_543_, lean_object* v_a_544_){
_start:
{
uint8_t v_nondep_2427__boxed_545_; lean_object* v_res_546_; 
v_nondep_2427__boxed_545_ = lean_unbox(v_nondep_531_);
v_res_546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_declName_530_, v_nondep_2427__boxed_545_, v_inst_532_, v_inst_533_, v_pre_534_, v_post_535_, v_x_536_, v_x_537_, v___y_538_, v_body_539_, v___y_540_, v_type_541_, v_value_542_, v_toBind_543_, v_a_544_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_547_; lean_object* v_dummy_548_; 
v___x_547_ = lean_box(0);
v_dummy_548_ = l_Lean_Expr_sort___override(v___x_547_);
return v_dummy_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_549_, lean_object* v_data_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_pre_553_, lean_object* v_post_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v_a_559_){
_start:
{
size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_ptr_addr(v_expr_549_);
v___x_561_ = lean_ptr_addr(v_a_559_);
v___x_562_ = lean_usize_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v___y_558_);
v___x_563_ = l_Lean_Expr_mdata___override(v_data_550_, v_a_559_);
v___x_564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_551_, v_inst_552_, v_pre_553_, v_post_554_, v_x_555_, v_x_556_, v___x_563_, v___y_557_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; 
lean_dec_ref(v_a_559_);
lean_dec(v_data_550_);
v___x_565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_551_, v_inst_552_, v_pre_553_, v_post_554_, v_x_555_, v_x_556_, v___y_558_, v___y_557_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_566_, lean_object* v_data_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_pre_570_, lean_object* v_post_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_566_, v_data_567_, v_inst_568_, v_inst_569_, v_pre_570_, v_post_571_, v_x_572_, v_x_573_, v___y_574_, v___y_575_, v_a_576_);
lean_dec_ref(v_expr_566_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_578_, lean_object* v_typeName_579_, lean_object* v_idx_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_pre_583_, lean_object* v_post_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v_a_589_){
_start:
{
size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_ptr_addr(v_struct_578_);
v___x_591_ = lean_ptr_addr(v_a_589_);
v___x_592_ = lean_usize_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v___y_588_);
v___x_593_ = l_Lean_Expr_proj___override(v_typeName_579_, v_idx_580_, v_a_589_);
v___x_594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_581_, v_inst_582_, v_pre_583_, v_post_584_, v_x_585_, v_x_586_, v___x_593_, v___y_587_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; 
lean_dec_ref(v_a_589_);
lean_dec(v_idx_580_);
lean_dec(v_typeName_579_);
v___x_595_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_581_, v_inst_582_, v_pre_583_, v_post_584_, v_x_585_, v_x_586_, v___y_588_, v___y_587_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_596_, lean_object* v_typeName_597_, lean_object* v_idx_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_pre_601_, lean_object* v_post_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_596_, v_typeName_597_, v_idx_598_, v_inst_599_, v_inst_600_, v_pre_601_, v_post_602_, v_x_603_, v_x_604_, v___y_605_, v___y_606_, v_a_607_);
lean_dec_ref(v_struct_596_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_pre_612_, lean_object* v_post_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_toBind_616_, lean_object* v___f_617_, lean_object* v_e_618_, lean_object* v_____do__lift_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___y_622_; 
switch(lean_obj_tag(v_____do__lift_619_))
{
case 0:
{
lean_object* v_e_667_; lean_object* v_toPure_668_; lean_object* v___x_669_; 
lean_dec(v___y_620_);
lean_dec_ref(v_e_618_);
lean_dec(v___f_617_);
lean_dec(v_toBind_616_);
lean_dec(v_x_615_);
lean_dec(v_post_613_);
lean_dec(v_pre_612_);
lean_dec_ref(v_inst_611_);
lean_dec_ref(v_inst_610_);
v_e_667_ = lean_ctor_get(v_____do__lift_619_, 0);
lean_inc_ref(v_e_667_);
lean_dec_ref(v_____do__lift_619_);
v_toPure_668_ = lean_ctor_get(v_toApplicative_609_, 1);
lean_inc(v_toPure_668_);
lean_dec_ref(v_toApplicative_609_);
v___x_669_ = lean_apply_2(v_toPure_668_, lean_box(0), v_e_667_);
return v___x_669_;
}
case 1:
{
lean_object* v_e_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec_ref(v_e_618_);
lean_dec(v___f_617_);
lean_dec_ref(v_toApplicative_609_);
v_e_670_ = lean_ctor_get(v_____do__lift_619_, 0);
lean_inc_ref(v_e_670_);
lean_dec_ref(v_____do__lift_619_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
v___f_671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7), 8, 7);
lean_closure_set(v___f_671_, 0, v_inst_610_);
lean_closure_set(v___f_671_, 1, v_inst_611_);
lean_closure_set(v___f_671_, 2, v_pre_612_);
lean_closure_set(v___f_671_, 3, v_post_613_);
lean_closure_set(v___f_671_, 4, v_x_614_);
lean_closure_set(v___f_671_, 5, v_x_615_);
lean_closure_set(v___f_671_, 6, v___y_620_);
v___x_672_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_e_670_, v___y_620_);
v___x_673_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_672_, v___f_671_);
return v___x_673_;
}
default: 
{
lean_object* v_e_x3f_674_; 
lean_dec_ref(v_toApplicative_609_);
v_e_x3f_674_ = lean_ctor_get(v_____do__lift_619_, 0);
lean_inc(v_e_x3f_674_);
lean_dec_ref(v_____do__lift_619_);
if (lean_obj_tag(v_e_x3f_674_) == 0)
{
v___y_622_ = v_e_618_;
goto v___jp_621_;
}
else
{
lean_object* v_val_675_; 
lean_dec_ref(v_e_618_);
v_val_675_ = lean_ctor_get(v_e_x3f_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref(v_e_x3f_674_);
v___y_622_ = v_val_675_;
goto v___jp_621_;
}
}
}
v___jp_621_:
{
switch(lean_obj_tag(v___y_622_))
{
case 7:
{
lean_object* v_binderName_623_; lean_object* v_binderType_624_; lean_object* v_body_625_; uint8_t v_binderInfo_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v___f_617_);
v_binderName_623_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_binderName_623_);
v_binderType_624_ = lean_ctor_get(v___y_622_, 1);
lean_inc_ref(v_binderType_624_);
v_body_625_ = lean_ctor_get(v___y_622_, 2);
lean_inc_ref(v_body_625_);
v_binderInfo_626_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 8);
v___x_627_ = lean_box(v_binderInfo_626_);
lean_inc(v_toBind_616_);
lean_inc_ref(v_binderType_624_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
v___f_628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_628_, 0, v_binderName_623_);
lean_closure_set(v___f_628_, 1, v___x_627_);
lean_closure_set(v___f_628_, 2, v_inst_610_);
lean_closure_set(v___f_628_, 3, v_inst_611_);
lean_closure_set(v___f_628_, 4, v_pre_612_);
lean_closure_set(v___f_628_, 5, v_post_613_);
lean_closure_set(v___f_628_, 6, v_x_614_);
lean_closure_set(v___f_628_, 7, v_x_615_);
lean_closure_set(v___f_628_, 8, v___y_620_);
lean_closure_set(v___f_628_, 9, v___y_622_);
lean_closure_set(v___f_628_, 10, v_binderType_624_);
lean_closure_set(v___f_628_, 11, v_body_625_);
lean_closure_set(v___f_628_, 12, v_toBind_616_);
v___x_629_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_binderType_624_, v___y_620_);
v___x_630_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_629_, v___f_628_);
return v___x_630_;
}
case 6:
{
lean_object* v_binderName_631_; lean_object* v_binderType_632_; lean_object* v_body_633_; uint8_t v_binderInfo_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v___f_617_);
v_binderName_631_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_binderName_631_);
v_binderType_632_ = lean_ctor_get(v___y_622_, 1);
lean_inc_ref(v_binderType_632_);
v_body_633_ = lean_ctor_get(v___y_622_, 2);
lean_inc_ref(v_body_633_);
v_binderInfo_634_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*3 + 8);
v___x_635_ = lean_box(v_binderInfo_634_);
lean_inc(v_toBind_616_);
lean_inc_ref(v_binderType_632_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 14, 13);
lean_closure_set(v___f_636_, 0, v_binderName_631_);
lean_closure_set(v___f_636_, 1, v___x_635_);
lean_closure_set(v___f_636_, 2, v_inst_610_);
lean_closure_set(v___f_636_, 3, v_inst_611_);
lean_closure_set(v___f_636_, 4, v_pre_612_);
lean_closure_set(v___f_636_, 5, v_post_613_);
lean_closure_set(v___f_636_, 6, v_x_614_);
lean_closure_set(v___f_636_, 7, v_x_615_);
lean_closure_set(v___f_636_, 8, v___y_620_);
lean_closure_set(v___f_636_, 9, v___y_622_);
lean_closure_set(v___f_636_, 10, v_binderType_632_);
lean_closure_set(v___f_636_, 11, v_body_633_);
lean_closure_set(v___f_636_, 12, v_toBind_616_);
v___x_637_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_binderType_632_, v___y_620_);
v___x_638_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_637_, v___f_636_);
return v___x_638_;
}
case 8:
{
lean_object* v_declName_639_; lean_object* v_type_640_; lean_object* v_value_641_; lean_object* v_body_642_; uint8_t v_nondep_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v___f_617_);
v_declName_639_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_declName_639_);
v_type_640_ = lean_ctor_get(v___y_622_, 1);
lean_inc_ref(v_type_640_);
v_value_641_ = lean_ctor_get(v___y_622_, 2);
lean_inc_ref(v_value_641_);
v_body_642_ = lean_ctor_get(v___y_622_, 3);
lean_inc_ref(v_body_642_);
v_nondep_643_ = lean_ctor_get_uint8(v___y_622_, sizeof(void*)*4 + 8);
v___x_644_ = lean_box(v_nondep_643_);
lean_inc(v_toBind_616_);
lean_inc_ref(v_type_640_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
v___f_645_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 15, 14);
lean_closure_set(v___f_645_, 0, v_declName_639_);
lean_closure_set(v___f_645_, 1, v___x_644_);
lean_closure_set(v___f_645_, 2, v_inst_610_);
lean_closure_set(v___f_645_, 3, v_inst_611_);
lean_closure_set(v___f_645_, 4, v_pre_612_);
lean_closure_set(v___f_645_, 5, v_post_613_);
lean_closure_set(v___f_645_, 6, v_x_614_);
lean_closure_set(v___f_645_, 7, v_x_615_);
lean_closure_set(v___f_645_, 8, v___y_620_);
lean_closure_set(v___f_645_, 9, v_body_642_);
lean_closure_set(v___f_645_, 10, v___y_622_);
lean_closure_set(v___f_645_, 11, v_type_640_);
lean_closure_set(v___f_645_, 12, v_value_641_);
lean_closure_set(v___f_645_, 13, v_toBind_616_);
v___x_646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_type_640_, v___y_620_);
v___x_647_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_646_, v___f_645_);
return v___x_647_;
}
case 5:
{
lean_object* v_dummy_648_; lean_object* v_nargs_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_2275__overap_653_; lean_object* v___x_654_; 
lean_dec(v_toBind_616_);
lean_dec(v_x_615_);
lean_dec(v_post_613_);
lean_dec(v_pre_612_);
lean_dec_ref(v_inst_611_);
lean_dec_ref(v_inst_610_);
v_dummy_648_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_649_ = l_Lean_Expr_getAppNumArgs(v___y_622_);
lean_inc(v_nargs_649_);
v___x_650_ = lean_mk_array(v_nargs_649_, v_dummy_648_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_sub(v_nargs_649_, v___x_651_);
lean_dec(v_nargs_649_);
v___x_2275__overap_653_ = l_Lean_Expr_withAppAux___redArg(v___f_617_, v___y_622_, v___x_650_, v___x_652_);
v___x_654_ = lean_apply_1(v___x_2275__overap_653_, v___y_620_);
return v___x_654_;
}
case 10:
{
lean_object* v_data_655_; lean_object* v_expr_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___f_617_);
v_data_655_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_data_655_);
v_expr_656_ = lean_ctor_get(v___y_622_, 1);
lean_inc_ref(v_expr_656_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
lean_inc_ref(v_expr_656_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 11, 10);
lean_closure_set(v___f_657_, 0, v_expr_656_);
lean_closure_set(v___f_657_, 1, v_data_655_);
lean_closure_set(v___f_657_, 2, v_inst_610_);
lean_closure_set(v___f_657_, 3, v_inst_611_);
lean_closure_set(v___f_657_, 4, v_pre_612_);
lean_closure_set(v___f_657_, 5, v_post_613_);
lean_closure_set(v___f_657_, 6, v_x_614_);
lean_closure_set(v___f_657_, 7, v_x_615_);
lean_closure_set(v___f_657_, 8, v___y_620_);
lean_closure_set(v___f_657_, 9, v___y_622_);
v___x_658_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_expr_656_, v___y_620_);
v___x_659_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_658_, v___f_657_);
return v___x_659_;
}
case 11:
{
lean_object* v_typeName_660_; lean_object* v_idx_661_; lean_object* v_struct_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v___f_617_);
v_typeName_660_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_typeName_660_);
v_idx_661_ = lean_ctor_get(v___y_622_, 1);
lean_inc(v_idx_661_);
v_struct_662_ = lean_ctor_get(v___y_622_, 2);
lean_inc_ref(v_struct_662_);
lean_inc(v___y_620_);
lean_inc(v_x_615_);
lean_inc(v_post_613_);
lean_inc(v_pre_612_);
lean_inc_ref(v_inst_611_);
lean_inc_ref(v_inst_610_);
lean_inc_ref(v_struct_662_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 12, 11);
lean_closure_set(v___f_663_, 0, v_struct_662_);
lean_closure_set(v___f_663_, 1, v_typeName_660_);
lean_closure_set(v___f_663_, 2, v_idx_661_);
lean_closure_set(v___f_663_, 3, v_inst_610_);
lean_closure_set(v___f_663_, 4, v_inst_611_);
lean_closure_set(v___f_663_, 5, v_pre_612_);
lean_closure_set(v___f_663_, 6, v_post_613_);
lean_closure_set(v___f_663_, 7, v_x_614_);
lean_closure_set(v___f_663_, 8, v_x_615_);
lean_closure_set(v___f_663_, 9, v___y_620_);
lean_closure_set(v___f_663_, 10, v___y_622_);
v___x_664_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v_struct_662_, v___y_620_);
v___x_665_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_664_, v___f_663_);
return v___x_665_;
}
default: 
{
lean_object* v___x_666_; 
lean_dec(v___f_617_);
lean_dec(v_toBind_616_);
v___x_666_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_610_, v_inst_611_, v_pre_612_, v_post_613_, v_x_614_, v_x_615_, v___y_622_, v___y_620_);
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_pre_678_, lean_object* v_post_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_e_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___f_687_; lean_object* v___x_688_; lean_object* v_toApplicative_689_; lean_object* v_toBind_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc_ref(v_inst_676_);
v___x_684_ = l_ReaderT_instMonad___redArg(v_inst_676_);
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0);
lean_inc_ref(v_inst_677_);
v___f_686_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_686_, 0, v___x_685_);
lean_closure_set(v___f_686_, 1, v_inst_677_);
lean_inc_ref(v_inst_677_);
v___f_687_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_687_, 0, v___x_685_);
lean_closure_set(v___f_687_, 1, v_inst_677_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___f_686_);
lean_ctor_set(v___x_688_, 1, v___f_687_);
v_toApplicative_689_ = lean_ctor_get(v_inst_676_, 0);
lean_inc_ref(v_toApplicative_689_);
v_toBind_690_ = lean_ctor_get(v_inst_676_, 1);
lean_inc(v_toBind_690_);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__2));
lean_inc(v_toBind_690_);
lean_inc(v_x_681_);
lean_inc(v_a_683_);
lean_inc_ref(v_e_682_);
lean_inc_ref(v_toApplicative_689_);
v___f_693_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_693_, 0, v_toApplicative_689_);
lean_closure_set(v___f_693_, 1, v___x_691_);
lean_closure_set(v___f_693_, 2, v___x_692_);
lean_closure_set(v___f_693_, 3, v_e_682_);
lean_closure_set(v___f_693_, 4, v_a_683_);
lean_closure_set(v___f_693_, 5, v_x_681_);
lean_closure_set(v___f_693_, 6, v_toBind_690_);
lean_inc_ref(v_e_682_);
lean_inc_ref(v_toApplicative_689_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_694_, 0, v_toApplicative_689_);
lean_closure_set(v___f_694_, 1, v___x_691_);
lean_closure_set(v___f_694_, 2, v___x_692_);
lean_closure_set(v___f_694_, 3, v_e_682_);
lean_inc(v_toBind_690_);
lean_inc_ref(v___x_684_);
lean_inc(v_x_681_);
lean_inc(v_post_679_);
lean_inc(v_pre_678_);
lean_inc_ref(v_inst_677_);
lean_inc_ref(v_inst_676_);
v___f_695_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6), 11, 8);
lean_closure_set(v___f_695_, 0, v_inst_676_);
lean_closure_set(v___f_695_, 1, v_inst_677_);
lean_closure_set(v___f_695_, 2, v_pre_678_);
lean_closure_set(v___f_695_, 3, v_post_679_);
lean_closure_set(v___f_695_, 4, v_x_680_);
lean_closure_set(v___f_695_, 5, v_x_681_);
lean_closure_set(v___f_695_, 6, v___x_684_);
lean_closure_set(v___f_695_, 7, v_toBind_690_);
lean_inc_ref(v_e_682_);
lean_inc(v_toBind_690_);
lean_inc(v_x_681_);
lean_inc(v_pre_678_);
lean_inc_ref(v_inst_676_);
lean_inc_ref(v_toApplicative_689_);
v___f_696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17), 12, 10);
lean_closure_set(v___f_696_, 0, v_toApplicative_689_);
lean_closure_set(v___f_696_, 1, v_inst_676_);
lean_closure_set(v___f_696_, 2, v_inst_677_);
lean_closure_set(v___f_696_, 3, v_pre_678_);
lean_closure_set(v___f_696_, 4, v_post_679_);
lean_closure_set(v___f_696_, 5, v_x_680_);
lean_closure_set(v___f_696_, 6, v_x_681_);
lean_closure_set(v___f_696_, 7, v_toBind_690_);
lean_closure_set(v___f_696_, 8, v___f_695_);
lean_closure_set(v___f_696_, 9, v_e_682_);
lean_inc(v_toBind_690_);
lean_inc(v_a_683_);
v___f_697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18), 11, 10);
lean_closure_set(v___f_697_, 0, v_pre_678_);
lean_closure_set(v___f_697_, 1, v_e_682_);
lean_closure_set(v___f_697_, 2, v_inst_676_);
lean_closure_set(v___f_697_, 3, v___f_696_);
lean_closure_set(v___f_697_, 4, v___x_684_);
lean_closure_set(v___f_697_, 5, v___x_688_);
lean_closure_set(v___f_697_, 6, v_a_683_);
lean_closure_set(v___f_697_, 7, v_toBind_690_);
lean_closure_set(v___f_697_, 8, v___f_693_);
lean_closure_set(v___f_697_, 9, v_toApplicative_689_);
v___x_698_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_698_, 0, lean_box(0));
lean_closure_set(v___x_698_, 1, lean_box(0));
lean_closure_set(v___x_698_, 2, v_a_683_);
v___x_699_ = lean_apply_2(v_x_681_, lean_box(0), v___x_698_);
lean_inc(v_toBind_690_);
v___x_700_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v___x_699_, v___f_694_);
v___x_701_ = lean_apply_4(v_toBind_690_, lean_box(0), lean_box(0), v___x_700_, v___f_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_pre_705_, lean_object* v_post_706_, lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_e_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___y_713_; 
switch(lean_obj_tag(v_a_711_))
{
case 0:
{
lean_object* v_e_716_; lean_object* v_toPure_717_; lean_object* v___x_718_; 
lean_dec_ref(v_e_710_);
lean_dec(v_a_709_);
lean_dec(v_x_708_);
lean_dec(v_post_706_);
lean_dec(v_pre_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
v_e_716_ = lean_ctor_get(v_a_711_, 0);
lean_inc_ref(v_e_716_);
lean_dec_ref(v_a_711_);
v_toPure_717_ = lean_ctor_get(v_toApplicative_702_, 1);
lean_inc(v_toPure_717_);
lean_dec_ref(v_toApplicative_702_);
v___x_718_ = lean_apply_2(v_toPure_717_, lean_box(0), v_e_716_);
return v___x_718_;
}
case 1:
{
lean_object* v_e_719_; lean_object* v___x_720_; 
lean_dec_ref(v_e_710_);
lean_dec_ref(v_toApplicative_702_);
v_e_719_ = lean_ctor_get(v_a_711_, 0);
lean_inc_ref(v_e_719_);
lean_dec_ref(v_a_711_);
v___x_720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_703_, v_inst_704_, v_pre_705_, v_post_706_, v_x_707_, v_x_708_, v_e_719_, v_a_709_);
return v___x_720_;
}
default: 
{
lean_object* v_e_x3f_721_; 
lean_dec(v_a_709_);
lean_dec(v_x_708_);
lean_dec(v_post_706_);
lean_dec(v_pre_705_);
lean_dec_ref(v_inst_704_);
lean_dec_ref(v_inst_703_);
v_e_x3f_721_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_e_x3f_721_);
lean_dec_ref(v_a_711_);
if (lean_obj_tag(v_e_x3f_721_) == 0)
{
v___y_713_ = v_e_710_;
goto v___jp_712_;
}
else
{
lean_object* v_val_722_; 
lean_dec_ref(v_e_710_);
v_val_722_ = lean_ctor_get(v_e_x3f_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v_e_x3f_721_);
v___y_713_ = v_val_722_;
goto v___jp_712_;
}
}
}
v___jp_712_:
{
lean_object* v_toPure_714_; lean_object* v___x_715_; 
v_toPure_714_ = lean_ctor_get(v_toApplicative_702_, 1);
lean_inc(v_toPure_714_);
lean_dec_ref(v_toApplicative_702_);
v___x_715_ = lean_apply_2(v_toPure_714_, lean_box(0), v___y_713_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_pre_725_, lean_object* v_post_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_e_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_toApplicative_731_; lean_object* v_toBind_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_toApplicative_731_ = lean_ctor_get(v_inst_723_, 0);
lean_inc_ref(v_toApplicative_731_);
v_toBind_732_ = lean_ctor_get(v_inst_723_, 1);
lean_inc(v_toBind_732_);
lean_inc_ref(v_e_729_);
lean_inc(v_post_726_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0), 10, 9);
lean_closure_set(v___f_733_, 0, v_toApplicative_731_);
lean_closure_set(v___f_733_, 1, v_inst_723_);
lean_closure_set(v___f_733_, 2, v_inst_724_);
lean_closure_set(v___f_733_, 3, v_pre_725_);
lean_closure_set(v___f_733_, 4, v_post_726_);
lean_closure_set(v___f_733_, 5, v_x_727_);
lean_closure_set(v___f_733_, 6, v_x_728_);
lean_closure_set(v___f_733_, 7, v_a_730_);
lean_closure_set(v___f_733_, 8, v_e_729_);
v___x_734_ = lean_apply_1(v_post_726_, v_e_729_);
v___x_735_ = lean_apply_4(v_toBind_732_, lean_box(0), lean_box(0), v___x_734_, v___f_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_pre_738_, lean_object* v_post_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_736_, v_inst_737_, v_pre_738_, v_post_739_, v_x_740_, v_x_741_, v_a_743_, v___y_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_pre_748_, lean_object* v_post_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_e_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_746_, v_inst_747_, v_pre_748_, v_post_749_, v_x_750_, v_x_751_, v_e_752_, v_a_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_pre_758_, lean_object* v_post_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_e_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_756_, v_inst_757_, v_pre_758_, v_post_759_, v_x_760_, v_x_761_, v_e_762_, v_a_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_apply_1(v_x_765_, lean_box(0));
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Core_transform___redArg___lam__0(v_x_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_772_, lean_object* v_00_u03b1_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_775_, 0, v_x_774_);
v___x_776_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_776_, 0, lean_box(0));
lean_closure_set(v___x_776_, 1, v___f_775_);
v___x_777_ = lean_apply_2(v_inst_772_, lean_box(0), v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_778_, lean_object* v_____x_779_){
_start:
{
lean_object* v_fst_780_; lean_object* v___x_781_; 
v_fst_780_ = lean_ctor_get(v_____x_779_, 0);
lean_inc(v_fst_780_);
lean_dec_ref(v_____x_779_);
v___x_781_ = lean_apply_2(v_toPure_778_, lean_box(0), v_fst_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_782_, lean_object* v_toPure_783_, lean_object* v_s_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_782_);
lean_ctor_set(v___x_785_, 1, v_s_784_);
v___x_786_ = lean_apply_2(v_toPure_783_, lean_box(0), v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_787_, lean_object* v_ref_788_, lean_object* v_x_789_, lean_object* v_toBind_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_792_, 0, v_a_791_);
lean_closure_set(v___f_792_, 1, v_toPure_787_);
v___x_793_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_793_, 0, lean_box(0));
lean_closure_set(v___x_793_, 1, lean_box(0));
lean_closure_set(v___x_793_, 2, v_ref_788_);
v___x_794_ = lean_apply_2(v_x_789_, lean_box(0), v___x_793_);
v___x_795_ = lean_apply_4(v_toBind_790_, lean_box(0), lean_box(0), v___x_794_, v___f_792_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_796_, lean_object* v_x_797_, lean_object* v_toBind_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_pre_801_, lean_object* v_post_802_, lean_object* v_x_803_, lean_object* v_input_804_, lean_object* v_ref_805_){
_start:
{
lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc(v_toBind_798_);
lean_inc(v_x_797_);
lean_inc(v_ref_805_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_806_, 0, v_toPure_796_);
lean_closure_set(v___f_806_, 1, v_ref_805_);
lean_closure_set(v___f_806_, 2, v_x_797_);
lean_closure_set(v___f_806_, 3, v_toBind_798_);
v___x_807_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_799_, v_inst_800_, v_pre_801_, v_post_802_, v_x_803_, v_x_797_, v_input_804_, v_ref_805_);
v___x_808_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v___x_807_, v___f_806_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_box(0);
v___x_810_ = lean_unsigned_to_nat(16u);
v___x_811_ = lean_mk_array(v___x_810_, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_816_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_816_, 0, lean_box(0));
lean_closure_set(v___x_816_, 1, lean_box(0));
lean_closure_set(v___x_816_, 2, v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_input_820_, lean_object* v_pre_821_, lean_object* v_post_822_){
_start:
{
lean_object* v_x_823_; lean_object* v_toApplicative_824_; lean_object* v_toBind_825_; lean_object* v_toPure_826_; lean_object* v_x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_x_823_ = lean_box(0);
v_toApplicative_824_ = lean_ctor_get(v_inst_817_, 0);
v_toBind_825_ = lean_ctor_get(v_inst_817_, 1);
lean_inc(v_toBind_825_);
v_toPure_826_ = lean_ctor_get(v_toApplicative_824_, 1);
lean_inc(v_toPure_826_);
lean_inc(v_inst_818_);
v_x_827_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_827_, 0, v_inst_818_);
v___x_828_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_829_ = l_Lean_Core_transform___redArg___lam__1(v_inst_818_, lean_box(0), v___x_828_);
lean_inc(v_toPure_826_);
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_830_, 0, v_toPure_826_);
lean_inc(v_toBind_825_);
v___f_831_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 10, 9);
lean_closure_set(v___f_831_, 0, v_toPure_826_);
lean_closure_set(v___f_831_, 1, v_x_827_);
lean_closure_set(v___f_831_, 2, v_toBind_825_);
lean_closure_set(v___f_831_, 3, v_inst_817_);
lean_closure_set(v___f_831_, 4, v_inst_819_);
lean_closure_set(v___f_831_, 5, v_pre_821_);
lean_closure_set(v___f_831_, 6, v_post_822_);
lean_closure_set(v___f_831_, 7, v_x_823_);
lean_closure_set(v___f_831_, 8, v_input_820_);
lean_inc(v_toBind_825_);
v___x_832_ = lean_apply_4(v_toBind_825_, lean_box(0), lean_box(0), v___x_829_, v___f_831_);
v___x_833_ = lean_apply_4(v_toBind_825_, lean_box(0), lean_box(0), v___x_832_, v___f_830_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_input_838_, lean_object* v_pre_839_, lean_object* v_post_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Core_transform___redArg(v_inst_835_, v_inst_836_, v_inst_837_, v_input_838_, v_pre_839_, v_post_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; uint8_t v___x_849_; 
v___x_848_ = 0;
v___x_849_ = l_Lean_Expr_isHeadBetaTarget(v_e_844_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v_e_844_);
v___x_850_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = l_Lean_Expr_headBeta(v_e_844_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Core_betaReduce___lam__0(v_e_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v_e_860_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Core_betaReduce___lam__1(v_e_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = l_Lean_maxRecDepthErrorMessage;
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_879_ = l_Lean_MessageData_ofFormat(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_881_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_882_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_883_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_ref_883_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___y_897_; lean_object* v_fileName_906_; lean_object* v_fileMap_907_; lean_object* v_options_908_; lean_object* v_currRecDepth_909_; lean_object* v_maxRecDepth_910_; lean_object* v_ref_911_; lean_object* v_currNamespace_912_; lean_object* v_openDecls_913_; lean_object* v_initHeartbeats_914_; lean_object* v_maxHeartbeats_915_; lean_object* v_quotContext_916_; lean_object* v_currMacroScope_917_; uint8_t v_diag_918_; lean_object* v_cancelTk_x3f_919_; uint8_t v_suppressElabErrors_920_; lean_object* v_inheritedTraceOptions_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_933_; 
v_fileName_906_ = lean_ctor_get(v___y_893_, 0);
v_fileMap_907_ = lean_ctor_get(v___y_893_, 1);
v_options_908_ = lean_ctor_get(v___y_893_, 2);
v_currRecDepth_909_ = lean_ctor_get(v___y_893_, 3);
v_maxRecDepth_910_ = lean_ctor_get(v___y_893_, 4);
v_ref_911_ = lean_ctor_get(v___y_893_, 5);
v_currNamespace_912_ = lean_ctor_get(v___y_893_, 6);
v_openDecls_913_ = lean_ctor_get(v___y_893_, 7);
v_initHeartbeats_914_ = lean_ctor_get(v___y_893_, 8);
v_maxHeartbeats_915_ = lean_ctor_get(v___y_893_, 9);
v_quotContext_916_ = lean_ctor_get(v___y_893_, 10);
v_currMacroScope_917_ = lean_ctor_get(v___y_893_, 11);
v_diag_918_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*14);
v_cancelTk_x3f_919_ = lean_ctor_get(v___y_893_, 12);
v_suppressElabErrors_920_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_921_ = lean_ctor_get(v___y_893_, 13);
v_isSharedCheck_933_ = !lean_is_exclusive(v___y_893_);
if (v_isSharedCheck_933_ == 0)
{
v___x_923_ = v___y_893_;
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_inheritedTraceOptions_921_);
lean_inc(v_cancelTk_x3f_919_);
lean_inc(v_currMacroScope_917_);
lean_inc(v_quotContext_916_);
lean_inc(v_maxHeartbeats_915_);
lean_inc(v_initHeartbeats_914_);
lean_inc(v_openDecls_913_);
lean_inc(v_currNamespace_912_);
lean_inc(v_ref_911_);
lean_inc(v_maxRecDepth_910_);
lean_inc(v_currRecDepth_909_);
lean_inc(v_options_908_);
lean_inc(v_fileMap_907_);
lean_inc(v_fileName_906_);
lean_dec(v___y_893_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
v___jp_896_:
{
if (lean_obj_tag(v___y_897_) == 0)
{
return v___y_897_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___y_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___y_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___y_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___y_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
v_resetjp_922_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_eq(v_currRecDepth_909_, v_maxRecDepth_910_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_currRecDepth_909_, v___x_926_);
lean_dec(v_currRecDepth_909_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 3, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fileName_906_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_fileMap_907_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_options_908_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_maxRecDepth_910_);
lean_ctor_set(v_reuseFailAlloc_931_, 5, v_ref_911_);
lean_ctor_set(v_reuseFailAlloc_931_, 6, v_currNamespace_912_);
lean_ctor_set(v_reuseFailAlloc_931_, 7, v_openDecls_913_);
lean_ctor_set(v_reuseFailAlloc_931_, 8, v_initHeartbeats_914_);
lean_ctor_set(v_reuseFailAlloc_931_, 9, v_maxHeartbeats_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 10, v_quotContext_916_);
lean_ctor_set(v_reuseFailAlloc_931_, 11, v_currMacroScope_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 12, v_cancelTk_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 13, v_inheritedTraceOptions_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*14, v_diag_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*14 + 1, v_suppressElabErrors_920_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_apply_4(v_x_891_, v___y_892_, v___x_929_, v___y_894_, lean_box(0));
v___y_897_ = v___x_930_;
goto v___jp_896_;
}
}
else
{
lean_object* v___x_932_; 
lean_del_object(v___x_923_);
lean_dec_ref(v_inheritedTraceOptions_921_);
lean_dec(v_cancelTk_x3f_919_);
lean_dec(v_currMacroScope_917_);
lean_dec(v_quotContext_916_);
lean_dec(v_maxHeartbeats_915_);
lean_dec(v_initHeartbeats_914_);
lean_dec(v_openDecls_913_);
lean_dec(v_currNamespace_912_);
lean_dec(v_maxRecDepth_910_);
lean_dec(v_currRecDepth_909_);
lean_dec_ref(v_options_908_);
lean_dec_ref(v_fileMap_907_);
lean_dec_ref(v_fileName_906_);
lean_dec(v___y_894_);
lean_dec(v___y_892_);
lean_dec_ref(v_x_891_);
v___x_932_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_911_);
v___y_897_ = v___x_932_;
goto v___jp_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_934_, v___y_935_, v___y_936_, v___y_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_apply_1(v_x_941_, lean_box(0));
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_947_, v_x_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_952_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
uint8_t v___x_955_; 
v___x_955_ = 0;
return v___x_955_;
}
else
{
lean_object* v_key_956_; lean_object* v_tail_957_; uint8_t v___x_958_; 
v_key_956_ = lean_ctor_get(v_x_954_, 0);
v_tail_957_ = lean_ctor_get(v_x_954_, 2);
v___x_958_ = l_Lean_ExprStructEq_beq(v_key_956_, v_a_953_);
if (v___x_958_ == 0)
{
v_x_954_ = v_tail_957_;
goto _start;
}
else
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_960_, lean_object* v_x_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_960_, v_x_961_);
lean_dec(v_x_961_);
lean_dec_ref(v_a_960_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
return v_x_964_;
}
else
{
lean_object* v_key_966_; lean_object* v_value_967_; lean_object* v_tail_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_991_; 
v_key_966_ = lean_ctor_get(v_x_965_, 0);
v_value_967_ = lean_ctor_get(v_x_965_, 1);
v_tail_968_ = lean_ctor_get(v_x_965_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_991_ == 0)
{
v___x_970_ = v_x_965_;
v_isShared_971_ = v_isSharedCheck_991_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_tail_968_);
lean_inc(v_value_967_);
lean_inc(v_key_966_);
lean_dec(v_x_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_991_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v___x_975_; uint64_t v_fold_976_; uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_972_ = lean_array_get_size(v_x_964_);
v___x_973_ = l_Lean_ExprStructEq_hash(v_key_966_);
v___x_974_ = 32ULL;
v___x_975_ = lean_uint64_shift_right(v___x_973_, v___x_974_);
v_fold_976_ = lean_uint64_xor(v___x_973_, v___x_975_);
v___x_977_ = 16ULL;
v___x_978_ = lean_uint64_shift_right(v_fold_976_, v___x_977_);
v___x_979_ = lean_uint64_xor(v_fold_976_, v___x_978_);
v___x_980_ = lean_uint64_to_usize(v___x_979_);
v___x_981_ = lean_usize_of_nat(v___x_972_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_sub(v___x_981_, v___x_982_);
v___x_984_ = lean_usize_land(v___x_980_, v___x_983_);
v___x_985_ = lean_array_uget_borrowed(v_x_964_, v___x_984_);
lean_inc(v___x_985_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 2, v___x_985_);
v___x_987_ = v___x_970_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_key_966_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_value_967_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v___x_985_);
v___x_987_ = v_reuseFailAlloc_990_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_array_uset(v_x_964_, v___x_984_, v___x_987_);
v_x_964_ = v___x_988_;
v_x_965_ = v_tail_968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_992_, lean_object* v_source_993_, lean_object* v_target_994_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_array_get_size(v_source_993_);
v___x_996_ = lean_nat_dec_lt(v_i_992_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v_source_993_);
lean_dec(v_i_992_);
return v_target_994_;
}
else
{
lean_object* v_es_997_; lean_object* v___x_998_; lean_object* v_source_999_; lean_object* v_target_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_es_997_ = lean_array_fget(v_source_993_, v_i_992_);
v___x_998_ = lean_box(0);
v_source_999_ = lean_array_fset(v_source_993_, v_i_992_, v___x_998_);
v_target_1000_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_994_, v_es_997_);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_i_992_, v___x_1001_);
lean_dec(v_i_992_);
v_i_992_ = v___x_1002_;
v_source_993_ = v_source_999_;
v_target_994_ = v_target_1000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_nbuckets_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1005_ = lean_array_get_size(v_data_1004_);
v___x_1006_ = lean_unsigned_to_nat(2u);
v_nbuckets_1007_ = lean_nat_mul(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_mk_array(v_nbuckets_1007_, v___x_1009_);
v___x_1011_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_1008_, v_data_1004_, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_x_1014_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_dec(v_b_1013_);
lean_dec_ref(v_a_1012_);
return v_x_1014_;
}
else
{
lean_object* v_key_1015_; lean_object* v_value_1016_; lean_object* v_tail_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1029_; 
v_key_1015_ = lean_ctor_get(v_x_1014_, 0);
v_value_1016_ = lean_ctor_get(v_x_1014_, 1);
v_tail_1017_ = lean_ctor_get(v_x_1014_, 2);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1014_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1019_ = v_x_1014_;
v_isShared_1020_ = v_isSharedCheck_1029_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_tail_1017_);
lean_inc(v_value_1016_);
lean_inc(v_key_1015_);
lean_dec(v_x_1014_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1029_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
uint8_t v___x_1021_; 
v___x_1021_ = l_Lean_ExprStructEq_beq(v_key_1015_, v_a_1012_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1012_, v_b_1013_, v_tail_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v___x_1022_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_key_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_value_1016_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1027_; 
lean_dec(v_value_1016_);
lean_dec(v_key_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_b_1013_);
lean_ctor_set(v___x_1019_, 0, v_a_1012_);
v___x_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1012_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_b_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_tail_1017_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v_size_1033_; lean_object* v_buckets_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1077_; 
v_size_1033_ = lean_ctor_get(v_m_1030_, 0);
v_buckets_1034_ = lean_ctor_get(v_m_1030_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_m_1030_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1036_ = v_m_1030_;
v_isShared_1037_ = v_isSharedCheck_1077_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_buckets_1034_);
lean_inc(v_size_1033_);
lean_dec(v_m_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1077_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v_fold_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; lean_object* v_bkt_1051_; uint8_t v___x_1052_; 
v___x_1038_ = lean_array_get_size(v_buckets_1034_);
v___x_1039_ = l_Lean_ExprStructEq_hash(v_a_1031_);
v___x_1040_ = 32ULL;
v___x_1041_ = lean_uint64_shift_right(v___x_1039_, v___x_1040_);
v_fold_1042_ = lean_uint64_xor(v___x_1039_, v___x_1041_);
v___x_1043_ = 16ULL;
v___x_1044_ = lean_uint64_shift_right(v_fold_1042_, v___x_1043_);
v___x_1045_ = lean_uint64_xor(v_fold_1042_, v___x_1044_);
v___x_1046_ = lean_uint64_to_usize(v___x_1045_);
v___x_1047_ = lean_usize_of_nat(v___x_1038_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_sub(v___x_1047_, v___x_1048_);
v___x_1050_ = lean_usize_land(v___x_1046_, v___x_1049_);
v_bkt_1051_ = lean_array_uget_borrowed(v_buckets_1034_, v___x_1050_);
v___x_1052_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1031_, v_bkt_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v_size_x27_1054_; lean_object* v___x_1055_; lean_object* v_buckets_x27_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1053_ = lean_unsigned_to_nat(1u);
v_size_x27_1054_ = lean_nat_add(v_size_1033_, v___x_1053_);
lean_dec(v_size_1033_);
lean_inc(v_bkt_1051_);
v___x_1055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1031_);
lean_ctor_set(v___x_1055_, 1, v_b_1032_);
lean_ctor_set(v___x_1055_, 2, v_bkt_1051_);
v_buckets_x27_1056_ = lean_array_uset(v_buckets_1034_, v___x_1050_, v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(4u);
v___x_1058_ = lean_nat_mul(v_size_x27_1054_, v___x_1057_);
v___x_1059_ = lean_unsigned_to_nat(3u);
v___x_1060_ = lean_nat_div(v___x_1058_, v___x_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_array_get_size(v_buckets_x27_1056_);
v___x_1062_ = lean_nat_dec_le(v___x_1060_, v___x_1061_);
lean_dec(v___x_1060_);
if (v___x_1062_ == 0)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; 
v_val_1063_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_1056_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_val_1063_);
lean_ctor_set(v___x_1036_, 0, v_size_x27_1054_);
v___x_1065_ = v___x_1036_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_size_x27_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_val_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
else
{
lean_object* v___x_1068_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_buckets_x27_1056_);
lean_ctor_set(v___x_1036_, 0, v_size_x27_1054_);
v___x_1068_ = v___x_1036_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_size_x27_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_buckets_x27_1056_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v_buckets_x27_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_inc(v_bkt_1051_);
v___x_1070_ = lean_box(0);
v_buckets_x27_1071_ = lean_array_uset(v_buckets_1034_, v___x_1050_, v___x_1070_);
v___x_1072_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1031_, v_b_1032_, v_bkt_1051_);
v___x_1073_ = lean_array_uset(v_buckets_x27_1071_, v___x_1050_, v___x_1072_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1073_);
v___x_1075_ = v___x_1036_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_size_1033_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1078_, lean_object* v_e_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = lean_st_ref_take(v_a_1078_);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1082_, v_e_1079_, v_a_1080_);
v___x_1084_ = lean_st_ref_set(v_a_1078_, v___x_1083_);
v___x_1085_ = lean_box(0);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1086_, lean_object* v_e_1087_, lean_object* v_a_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1086_, v_e_1087_, v_a_1088_);
lean_dec(v_a_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v_key_1094_; lean_object* v_value_1095_; lean_object* v_tail_1096_; uint8_t v___x_1097_; 
v_key_1094_ = lean_ctor_get(v_x_1092_, 0);
v_value_1095_ = lean_ctor_get(v_x_1092_, 1);
v_tail_1096_ = lean_ctor_get(v_x_1092_, 2);
v___x_1097_ = l_Lean_ExprStructEq_beq(v_key_1094_, v_a_1091_);
if (v___x_1097_ == 0)
{
v_x_1092_ = v_tail_1096_;
goto _start;
}
else
{
lean_object* v___x_1099_; 
lean_inc(v_value_1095_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_value_1095_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1100_, v_x_1101_);
lean_dec(v_x_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_buckets_1105_; lean_object* v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v_fold_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_buckets_1105_ = lean_ctor_get(v_m_1103_, 1);
v___x_1106_ = lean_array_get_size(v_buckets_1105_);
v___x_1107_ = l_Lean_ExprStructEq_hash(v_a_1104_);
v___x_1108_ = 32ULL;
v___x_1109_ = lean_uint64_shift_right(v___x_1107_, v___x_1108_);
v_fold_1110_ = lean_uint64_xor(v___x_1107_, v___x_1109_);
v___x_1111_ = 16ULL;
v___x_1112_ = lean_uint64_shift_right(v_fold_1110_, v___x_1111_);
v___x_1113_ = lean_uint64_xor(v_fold_1110_, v___x_1112_);
v___x_1114_ = lean_uint64_to_usize(v___x_1113_);
v___x_1115_ = lean_usize_of_nat(v___x_1106_);
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_sub(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_usize_land(v___x_1114_, v___x_1117_);
v___x_1119_ = lean_array_uget_borrowed(v_buckets_1105_, v___x_1118_);
v___x_1120_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1104_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1121_, v_a_1122_);
lean_dec_ref(v_a_1122_);
lean_dec_ref(v_m_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1124_, lean_object* v_post_1125_, size_t v_sz_1126_, size_t v_i_1127_, lean_object* v_bs_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_lt(v_i_1127_, v_sz_1126_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v_post_1125_);
lean_dec_ref(v_pre_1124_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_bs_1128_);
return v___x_1134_;
}
else
{
lean_object* v_v_1135_; lean_object* v___x_1136_; 
v_v_1135_ = lean_array_uget_borrowed(v_bs_1128_, v_i_1127_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1129_);
lean_inc(v_v_1135_);
lean_inc_ref(v_post_1125_);
lean_inc_ref(v_pre_1124_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1124_, v_post_1125_, v_v_1135_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; lean_object* v_bs_x27_1139_; size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v_bs_x27_1139_ = lean_array_uset(v_bs_1128_, v_i_1127_, v___x_1138_);
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1127_, v___x_1140_);
v___x_1142_ = lean_array_uset(v_bs_x27_1139_, v_i_1127_, v_a_1137_);
v_i_1127_ = v___x_1141_;
v_bs_1128_ = v___x_1142_;
goto _start;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v_bs_1128_);
lean_dec_ref(v_post_1125_);
lean_dec_ref(v_pre_1124_);
v_a_1144_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1136_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1136_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1152_, lean_object* v_post_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 5)
{
lean_object* v_fn_1161_; lean_object* v_arg_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_fn_1161_ = lean_ctor_get(v_x_1154_, 0);
lean_inc_ref(v_fn_1161_);
v_arg_1162_ = lean_ctor_get(v_x_1154_, 1);
lean_inc_ref(v_arg_1162_);
lean_dec_ref(v_x_1154_);
v___x_1163_ = lean_array_set(v_x_1155_, v_x_1156_, v_arg_1162_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_x_1156_, v___x_1164_);
lean_dec(v_x_1156_);
v_x_1154_ = v_fn_1161_;
v_x_1155_ = v___x_1163_;
v_x_1156_ = v___x_1165_;
goto _start;
}
else
{
lean_object* v___x_1167_; 
lean_dec(v_x_1156_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc_ref(v_post_1153_);
lean_inc_ref(v_pre_1152_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1152_, v_post_1153_, v_x_1154_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; size_t v_sz_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1167_);
v_sz_1169_ = lean_array_size(v_x_1155_);
v___x_1170_ = ((size_t)0ULL);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc_ref(v_post_1153_);
lean_inc_ref(v_pre_1152_);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1152_, v_post_1153_, v_sz_1169_, v___x_1170_, v_x_1155_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = l_Lean_mkAppN(v_a_1168_, v_a_1172_);
lean_dec(v_a_1172_);
v___x_1174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1152_, v_post_1153_, v___x_1173_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1174_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1168_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v_post_1153_);
lean_dec_ref(v_pre_1152_);
v_a_1175_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1171_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1171_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v_x_1155_);
lean_dec_ref(v_post_1153_);
lean_dec_ref(v_pre_1152_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v_pre_1183_, lean_object* v_e_1184_, lean_object* v_post_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1198_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; lean_object* v___x_1233_; 
lean_inc_ref(v_pre_1183_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc_ref(v_e_1184_);
v___x_1233_ = lean_apply_4(v_pre_1183_, v_e_1184_, v___y_1187_, v___y_1188_, lean_box(0));
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1323_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1323_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1323_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___y_1239_; 
switch(lean_obj_tag(v_a_1234_))
{
case 0:
{
lean_object* v_e_1313_; lean_object* v___x_1315_; 
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_pre_1183_);
v_e_1313_ = lean_ctor_get(v_a_1234_, 0);
lean_inc_ref(v_e_1313_);
lean_dec_ref(v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_e_1313_);
v___x_1315_ = v___x_1236_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_e_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
case 1:
{
lean_object* v_e_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1236_);
lean_dec_ref(v_e_1184_);
v_e_1317_ = lean_ctor_get(v_a_1234_, 0);
lean_inc_ref(v_e_1317_);
lean_dec_ref(v_a_1234_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1318_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_e_1317_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v_a_1319_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1320_;
}
else
{
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1318_;
}
}
default: 
{
lean_object* v_e_x3f_1321_; 
lean_del_object(v___x_1236_);
v_e_x3f_1321_ = lean_ctor_get(v_a_1234_, 0);
lean_inc(v_e_x3f_1321_);
lean_dec_ref(v_a_1234_);
if (lean_obj_tag(v_e_x3f_1321_) == 0)
{
v___y_1239_ = v_e_1184_;
goto v___jp_1238_;
}
else
{
lean_object* v_val_1322_; 
lean_dec_ref(v_e_1184_);
v_val_1322_ = lean_ctor_get(v_e_x3f_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref(v_e_x3f_1321_);
v___y_1239_ = v_val_1322_;
goto v___jp_1238_;
}
}
}
v___jp_1238_:
{
switch(lean_obj_tag(v___y_1239_))
{
case 7:
{
lean_object* v_binderName_1240_; lean_object* v_binderType_1241_; lean_object* v_body_1242_; uint8_t v_binderInfo_1243_; lean_object* v___x_1244_; 
v_binderName_1240_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_binderName_1240_);
v_binderType_1241_ = lean_ctor_get(v___y_1239_, 1);
v_body_1242_ = lean_ctor_get(v___y_1239_, 2);
v_binderInfo_1243_ = lean_ctor_get_uint8(v___y_1239_, sizeof(void*)*3 + 8);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_binderType_1241_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1244_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_binderType_1241_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_body_1242_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1246_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_body_1242_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; size_t v___x_1248_; size_t v___x_1249_; uint8_t v___x_1250_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_ptr_addr(v_binderType_1241_);
v___x_1249_ = lean_ptr_addr(v_a_1245_);
v___x_1250_ = lean_usize_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
v___y_1221_ = v_a_1247_;
v___y_1222_ = v___y_1239_;
v___y_1223_ = v_binderName_1240_;
v___y_1224_ = v_binderInfo_1243_;
v___y_1225_ = v_a_1245_;
v___y_1226_ = v___x_1250_;
goto v___jp_1220_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_ptr_addr(v_body_1242_);
v___x_1252_ = lean_ptr_addr(v_a_1247_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
v___y_1221_ = v_a_1247_;
v___y_1222_ = v___y_1239_;
v___y_1223_ = v_binderName_1240_;
v___y_1224_ = v_binderInfo_1243_;
v___y_1225_ = v_a_1245_;
v___y_1226_ = v___x_1253_;
goto v___jp_1220_;
}
}
else
{
lean_dec(v_a_1245_);
lean_dec_ref(v___y_1239_);
lean_dec(v_binderName_1240_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1246_;
}
}
else
{
lean_dec_ref(v___y_1239_);
lean_dec(v_binderName_1240_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1244_;
}
}
case 6:
{
lean_object* v_binderName_1254_; lean_object* v_binderType_1255_; lean_object* v_body_1256_; uint8_t v_binderInfo_1257_; lean_object* v___x_1258_; 
v_binderName_1254_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_binderName_1254_);
v_binderType_1255_ = lean_ctor_get(v___y_1239_, 1);
v_body_1256_ = lean_ctor_get(v___y_1239_, 2);
v_binderInfo_1257_ = lean_ctor_get_uint8(v___y_1239_, sizeof(void*)*3 + 8);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_binderType_1255_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_binderType_1255_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_body_1256_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_body_1256_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; size_t v___x_1262_; size_t v___x_1263_; uint8_t v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = lean_ptr_addr(v_binderType_1255_);
v___x_1263_ = lean_ptr_addr(v_a_1259_);
v___x_1264_ = lean_usize_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1208_ = v_binderName_1254_;
v___y_1209_ = v___y_1239_;
v___y_1210_ = v_a_1261_;
v___y_1211_ = v_a_1259_;
v___y_1212_ = v_binderInfo_1257_;
v___y_1213_ = v___x_1264_;
goto v___jp_1207_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_ptr_addr(v_body_1256_);
v___x_1266_ = lean_ptr_addr(v_a_1261_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
v___y_1208_ = v_binderName_1254_;
v___y_1209_ = v___y_1239_;
v___y_1210_ = v_a_1261_;
v___y_1211_ = v_a_1259_;
v___y_1212_ = v_binderInfo_1257_;
v___y_1213_ = v___x_1267_;
goto v___jp_1207_;
}
}
else
{
lean_dec(v_a_1259_);
lean_dec_ref(v___y_1239_);
lean_dec(v_binderName_1254_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1260_;
}
}
else
{
lean_dec_ref(v___y_1239_);
lean_dec(v_binderName_1254_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1258_;
}
}
case 8:
{
lean_object* v_declName_1268_; lean_object* v_type_1269_; lean_object* v_value_1270_; lean_object* v_body_1271_; uint8_t v_nondep_1272_; lean_object* v___x_1273_; 
v_declName_1268_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_declName_1268_);
v_type_1269_ = lean_ctor_get(v___y_1239_, 1);
v_value_1270_ = lean_ctor_get(v___y_1239_, 2);
v_body_1271_ = lean_ctor_get(v___y_1239_, 3);
lean_inc_ref(v_body_1271_);
v_nondep_1272_ = lean_ctor_get_uint8(v___y_1239_, sizeof(void*)*4 + 8);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_type_1269_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1273_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_type_1269_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_value_1270_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_value_1270_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_body_1271_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1277_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_body_1271_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; size_t v___x_1279_; size_t v___x_1280_; uint8_t v___x_1281_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_ptr_addr(v_type_1269_);
v___x_1280_ = lean_ptr_addr(v_a_1274_);
v___x_1281_ = lean_usize_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
v___y_1191_ = v_declName_1268_;
v___y_1192_ = v_a_1274_;
v___y_1193_ = v_body_1271_;
v___y_1194_ = v_a_1278_;
v___y_1195_ = v___y_1239_;
v___y_1196_ = v_a_1276_;
v___y_1197_ = v_nondep_1272_;
v___y_1198_ = v___x_1281_;
goto v___jp_1190_;
}
else
{
size_t v___x_1282_; size_t v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_ptr_addr(v_value_1270_);
v___x_1283_ = lean_ptr_addr(v_a_1276_);
v___x_1284_ = lean_usize_dec_eq(v___x_1282_, v___x_1283_);
v___y_1191_ = v_declName_1268_;
v___y_1192_ = v_a_1274_;
v___y_1193_ = v_body_1271_;
v___y_1194_ = v_a_1278_;
v___y_1195_ = v___y_1239_;
v___y_1196_ = v_a_1276_;
v___y_1197_ = v_nondep_1272_;
v___y_1198_ = v___x_1284_;
goto v___jp_1190_;
}
}
else
{
lean_dec(v_a_1276_);
lean_dec(v_a_1274_);
lean_dec_ref(v_body_1271_);
lean_dec(v_declName_1268_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1277_;
}
}
else
{
lean_dec(v_a_1274_);
lean_dec_ref(v_body_1271_);
lean_dec(v_declName_1268_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1275_;
}
}
else
{
lean_dec_ref(v_body_1271_);
lean_dec(v_declName_1268_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1273_;
}
}
case 5:
{
lean_object* v_dummy_1285_; lean_object* v_nargs_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_dummy_1285_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1286_ = l_Lean_Expr_getAppNumArgs(v___y_1239_);
lean_inc(v_nargs_1286_);
v___x_1287_ = lean_mk_array(v_nargs_1286_, v_dummy_1285_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_sub(v_nargs_1286_, v___x_1288_);
lean_dec(v_nargs_1286_);
v___x_1290_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1183_, v_post_1185_, v___y_1239_, v___x_1287_, v___x_1289_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1290_;
}
case 10:
{
lean_object* v_data_1291_; lean_object* v_expr_1292_; lean_object* v___x_1293_; 
v_data_1291_ = lean_ctor_get(v___y_1239_, 0);
v_expr_1292_ = lean_ctor_get(v___y_1239_, 1);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_expr_1292_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1293_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_expr_1292_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; size_t v___x_1295_; size_t v___x_1296_; uint8_t v___x_1297_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = lean_ptr_addr(v_expr_1292_);
v___x_1296_ = lean_ptr_addr(v_a_1294_);
v___x_1297_ = lean_usize_dec_eq(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_inc(v_data_1291_);
lean_dec_ref(v___y_1239_);
v___x_1298_ = l_Lean_Expr_mdata___override(v_data_1291_, v_a_1294_);
v___x_1299_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1298_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; 
lean_dec(v_a_1294_);
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1239_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1300_;
}
}
else
{
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1293_;
}
}
case 11:
{
lean_object* v_typeName_1301_; lean_object* v_idx_1302_; lean_object* v_struct_1303_; lean_object* v___x_1304_; 
v_typeName_1301_ = lean_ctor_get(v___y_1239_, 0);
v_idx_1302_ = lean_ctor_get(v___y_1239_, 1);
v_struct_1303_ = lean_ctor_get(v___y_1239_, 2);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v_struct_1303_);
lean_inc_ref(v_post_1185_);
lean_inc_ref(v_pre_1183_);
v___x_1304_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1183_, v_post_1185_, v_struct_1303_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; size_t v___x_1306_; size_t v___x_1307_; uint8_t v___x_1308_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = lean_ptr_addr(v_struct_1303_);
v___x_1307_ = lean_ptr_addr(v_a_1305_);
v___x_1308_ = lean_usize_dec_eq(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_inc(v_idx_1302_);
lean_inc(v_typeName_1301_);
lean_dec_ref(v___y_1239_);
v___x_1309_ = l_Lean_Expr_proj___override(v_typeName_1301_, v_idx_1302_, v_a_1305_);
v___x_1310_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1309_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
lean_dec(v_a_1305_);
v___x_1311_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1239_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1311_;
}
}
else
{
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1183_);
return v___x_1304_;
}
}
default: 
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1239_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1312_;
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_pre_1183_);
v_a_1324_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1233_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1233_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
v___jp_1190_:
{
if (v___y_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1193_);
v___x_1199_ = l_Lean_Expr_letE___override(v___y_1191_, v___y_1192_, v___y_1196_, v___y_1194_, v___y_1197_);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1199_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1200_;
}
else
{
size_t v___x_1201_; size_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_ptr_addr(v___y_1193_);
lean_dec_ref(v___y_1193_);
v___x_1202_ = lean_ptr_addr(v___y_1194_);
v___x_1203_ = lean_usize_dec_eq(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v___y_1195_);
v___x_1204_ = l_Lean_Expr_letE___override(v___y_1191_, v___y_1192_, v___y_1196_, v___y_1194_, v___y_1197_);
v___x_1205_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1204_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; 
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
v___x_1206_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1195_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1206_;
}
}
}
v___jp_1207_:
{
if (v___y_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v___y_1209_);
v___x_1214_ = l_Lean_Expr_lam___override(v___y_1208_, v___y_1211_, v___y_1210_, v___y_1212_);
v___x_1215_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1214_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
v___x_1216_ = l_Lean_instBEqBinderInfo_beq(v___y_1212_, v___y_1212_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v___y_1209_);
v___x_1217_ = l_Lean_Expr_lam___override(v___y_1208_, v___y_1211_, v___y_1210_, v___y_1212_);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1217_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; 
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1208_);
v___x_1219_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1209_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1219_;
}
}
}
v___jp_1220_:
{
if (v___y_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v___y_1222_);
v___x_1227_ = l_Lean_Expr_forallE___override(v___y_1223_, v___y_1225_, v___y_1221_, v___y_1224_);
v___x_1228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1227_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1228_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Lean_instBEqBinderInfo_beq(v___y_1224_, v___y_1224_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v___y_1222_);
v___x_1230_ = l_Lean_Expr_forallE___override(v___y_1223_, v___y_1225_, v___y_1221_, v___y_1224_);
v___x_1231_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___x_1230_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; 
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1221_);
v___x_1232_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1183_, v_post_1185_, v___y_1222_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_1332_, lean_object* v_e_1333_, lean_object* v_post_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v_pre_1332_, v_e_1333_, v_post_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1340_, lean_object* v_post_1341_, lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_inc(v_a_1343_);
v___x_1347_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1347_, 0, lean_box(0));
lean_closure_set(v___x_1347_, 1, lean_box(0));
lean_closure_set(v___x_1347_, 2, v_a_1343_);
v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1347_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1379_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1379_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1379_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1349_, v_e_1342_);
lean_dec(v_a_1349_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___f_1354_; lean_object* v___x_1355_; 
lean_del_object(v___x_1351_);
lean_inc_ref(v_e_1342_);
v___f_1354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_1354_, 0, v_pre_1340_);
lean_closure_set(v___f_1354_, 1, v_e_1342_);
lean_closure_set(v___f_1354_, 2, v_post_1341_);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v_a_1343_);
v___x_1355_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1354_, v_a_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref(v___x_1355_);
lean_inc(v_a_1356_);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1357_, 0, v_a_1343_);
lean_closure_set(v___f_1357_, 1, v_e_1342_);
lean_closure_set(v___f_1357_, 2, v_a_1356_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1357_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v___x_1358_, 0);
lean_dec(v_unused_1366_);
v___x_1360_ = v___x_1358_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_dec(v___x_1358_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_a_1356_);
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1356_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_a_1356_);
v_a_1367_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1358_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1358_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_e_1342_);
return v___x_1355_;
}
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1377_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_e_1342_);
lean_dec_ref(v_post_1341_);
lean_dec_ref(v_pre_1340_);
v_val_1375_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1375_);
lean_dec_ref(v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_val_1375_);
v___x_1377_ = v___x_1351_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_e_1342_);
lean_dec_ref(v_post_1341_);
lean_dec_ref(v_pre_1340_);
v_a_1380_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1348_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1348_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1388_, lean_object* v_post_1389_, lean_object* v_e_1390_, lean_object* v_a_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
lean_inc_ref(v_post_1389_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc_ref(v_e_1390_);
v___x_1395_ = lean_apply_4(v_post_1389_, v_e_1390_, v___y_1392_, v___y_1393_, lean_box(0));
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1414_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1414_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1414_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
switch(lean_obj_tag(v_a_1396_))
{
case 0:
{
lean_object* v_e_1400_; lean_object* v___x_1402_; 
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_e_1390_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
v_e_1400_ = lean_ctor_get(v_a_1396_, 0);
lean_inc_ref(v_e_1400_);
lean_dec_ref(v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_e_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_e_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
case 1:
{
lean_object* v_e_1404_; lean_object* v___x_1405_; 
lean_del_object(v___x_1398_);
lean_dec_ref(v_e_1390_);
v_e_1404_ = lean_ctor_get(v_a_1396_, 0);
lean_inc_ref(v_e_1404_);
lean_dec_ref(v_a_1396_);
v___x_1405_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1388_, v_post_1389_, v_e_1404_, v_a_1391_, v___y_1392_, v___y_1393_);
return v___x_1405_;
}
default: 
{
lean_object* v_e_x3f_1406_; 
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
v_e_x3f_1406_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_e_x3f_1406_);
lean_dec_ref(v_a_1396_);
if (lean_obj_tag(v_e_x3f_1406_) == 0)
{
lean_object* v___x_1408_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_e_1390_);
v___x_1408_ = v___x_1398_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_e_1390_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v_val_1410_; lean_object* v___x_1412_; 
lean_dec_ref(v_e_1390_);
v_val_1410_ = lean_ctor_get(v_e_x3f_1406_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v_e_x3f_1406_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_val_1410_);
v___x_1412_ = v___x_1398_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_val_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_e_1390_);
lean_dec_ref(v_post_1389_);
lean_dec_ref(v_pre_1388_);
v_a_1415_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1395_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1395_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1423_, lean_object* v_post_1424_, lean_object* v_e_1425_, lean_object* v_a_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1423_, v_post_1424_, v_e_1425_, v_a_1426_, v___y_1427_, v___y_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1431_, lean_object* v_post_1432_, lean_object* v_sz_1433_, lean_object* v_i_1434_, lean_object* v_bs_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1433_);
lean_dec(v_sz_1433_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1431_, v_post_1432_, v_sz_boxed_1440_, v_i_boxed_1441_, v_bs_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1443_, lean_object* v_post_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1443_, v_post_1444_, v_x_1445_, v_x_1446_, v_x_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1453_, lean_object* v_post_1454_, lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1453_, v_post_1454_, v_e_1455_, v_a_1456_, v___y_1457_, v___y_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_apply_1(v_x_1462_, lean_box(0));
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1468_, v_x_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1474_, lean_object* v_pre_1475_, lean_object* v_post_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1483_; 
v___x_1480_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1481_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1480_, v___y_1477_, v___y_1478_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v_a_1482_);
v___x_1483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1475_, v_post_1476_, v_input_1474_, v_a_1482_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1485_, 0, lean_box(0));
lean_closure_set(v___x_1485_, 1, lean_box(0));
lean_closure_set(v___x_1485_, 2, v_a_1482_);
v___x_1486_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1485_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1494_);
v___x_1488_ = v___x_1486_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v___x_1486_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_a_1484_);
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1484_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_dec(v_a_1482_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1495_, lean_object* v_pre_1496_, lean_object* v_post_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1495_, v_pre_1496_, v_post_1497_, v___y_1498_, v___y_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___f_1508_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1509_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1510_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1504_, v___f_1508_, v___f_1509_, v_a_1505_, v_a_1506_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Core_betaReduce(v_e_1511_, v_a_1512_, v_a_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1516_, lean_object* v_m_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1517_, v_a_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1520_, lean_object* v_m_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1520_, v_m_1521_, v_a_1522_);
lean_dec_ref(v_a_1522_);
lean_dec_ref(v_m_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1524_, lean_object* v_ref_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1525_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_ref_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1530_, v_ref_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1543_, v_x_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1550_, lean_object* v_m_1551_, lean_object* v_a_1552_, lean_object* v_b_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1551_, v_a_1552_, v_b_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1555_, lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1556_, v_x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1559_, lean_object* v_a_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1559_, v_a_1560_, v_x_1561_);
lean_dec(v_x_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1563_, lean_object* v_a_1564_, lean_object* v_x_1565_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1564_, v_x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1567_, lean_object* v_a_1568_, lean_object* v_x_1569_){
_start:
{
uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_res_1570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1567_, v_a_1568_, v_x_1569_);
lean_dec(v_x_1569_);
lean_dec_ref(v_a_1568_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1572_, lean_object* v_data_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1575_, lean_object* v_a_1576_, lean_object* v_b_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1576_, v_b_1577_, v_x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1580_, lean_object* v_i_1581_, lean_object* v_source_1582_, lean_object* v_target_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1581_, v_source_1582_, v_target_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1586_, v_x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_toPure_1591_; lean_object* v___x_1592_; 
v_toPure_1591_ = lean_ctor_get(v_toApplicative_1589_, 1);
lean_inc(v_toPure_1591_);
lean_dec_ref(v_toApplicative_1589_);
v___x_1592_ = lean_apply_2(v_toPure_1591_, lean_box(0), v_a_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_pre_1593_, lean_object* v_e_1594_, lean_object* v_inst_1595_, lean_object* v___f_1596_, lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v_a_1599_, lean_object* v_toBind_1600_, lean_object* v___f_1601_, lean_object* v_toApplicative_1602_, lean_object* v_a_1603_){
_start:
{
if (lean_obj_tag(v_a_1603_) == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_4020__overap_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_toApplicative_1602_);
v___x_1604_ = lean_apply_1(v_pre_1593_, v_e_1594_);
v___x_1605_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1605_, 0, lean_box(0));
lean_closure_set(v___x_1605_, 1, lean_box(0));
lean_closure_set(v___x_1605_, 2, lean_box(0));
lean_closure_set(v___x_1605_, 3, lean_box(0));
lean_closure_set(v___x_1605_, 4, v___x_1604_);
v___x_1606_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_1606_, 0, lean_box(0));
lean_closure_set(v___x_1606_, 1, lean_box(0));
lean_closure_set(v___x_1606_, 2, v_inst_1595_);
lean_closure_set(v___x_1606_, 3, lean_box(0));
lean_closure_set(v___x_1606_, 4, lean_box(0));
lean_closure_set(v___x_1606_, 5, v___x_1605_);
lean_closure_set(v___x_1606_, 6, v___f_1596_);
v___x_4020__overap_1607_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1597_, v___x_1598_, v___x_1606_);
v___x_1608_ = lean_apply_1(v___x_4020__overap_1607_, v_a_1599_);
v___x_1609_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v___x_1608_, v___f_1601_);
return v___x_1609_;
}
else
{
lean_object* v_val_1610_; lean_object* v_toPure_1611_; lean_object* v___x_1612_; 
lean_dec(v___f_1601_);
lean_dec(v_toBind_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v___x_1598_);
lean_dec_ref(v___x_1597_);
lean_dec(v___f_1596_);
lean_dec_ref(v_inst_1595_);
lean_dec_ref(v_e_1594_);
lean_dec(v_pre_1593_);
v_val_1610_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_val_1610_);
lean_dec_ref(v_a_1603_);
v_toPure_1611_ = lean_ctor_get(v_toApplicative_1602_, 1);
lean_inc(v_toPure_1611_);
lean_dec_ref(v_toApplicative_1602_);
v___x_1612_ = lean_apply_2(v_toPure_1611_, lean_box(0), v_val_1610_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_declName_1615_, lean_object* v_a_1616_, lean_object* v___f_1617_, uint8_t v_nondep_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
uint8_t v___x_1621_; lean_object* v___x_4040__overap_1622_; lean_object* v___x_1623_; 
v___x_1621_ = 0;
v___x_4040__overap_1622_ = l_Lean_Meta_withLetDecl___redArg(v___x_1613_, v___x_1614_, v_declName_1615_, v_a_1616_, v_a_1620_, v___f_1617_, v_nondep_1618_, v___x_1621_);
v___x_1623_ = lean_apply_1(v___x_4040__overap_1622_, v_a_1619_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_declName_1626_, lean_object* v_a_1627_, lean_object* v___f_1628_, lean_object* v_nondep_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
uint8_t v_nondep_4182__boxed_1632_; lean_object* v_res_1633_; 
v_nondep_4182__boxed_1632_ = lean_unbox(v_nondep_1629_);
v_res_1633_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1624_, v___x_1625_, v_declName_1626_, v_a_1627_, v___f_1628_, v_nondep_4182__boxed_1632_, v_a_1630_, v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1634_, uint8_t v_usedLetOnly_1635_, lean_object* v_inst_1636_, lean_object* v_toBind_1637_, lean_object* v___f_1638_, lean_object* v_a_1639_){
_start:
{
uint8_t v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1640_ = 0;
v___x_1641_ = 1;
v___x_1642_ = lean_box(v_usedLetOnly_1635_);
v___x_1643_ = lean_box(v___x_1640_);
v___x_1644_ = lean_box(v___x_1641_);
v___x_1645_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1645_, 0, v_fvars_1634_);
lean_closure_set(v___x_1645_, 1, v_a_1639_);
lean_closure_set(v___x_1645_, 2, v___x_1642_);
lean_closure_set(v___x_1645_, 3, v___x_1643_);
lean_closure_set(v___x_1645_, 4, v___x_1644_);
v___x_1646_ = lean_apply_2(v_inst_1636_, lean_box(0), v___x_1645_);
v___x_1647_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1646_, v___f_1638_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1648_, lean_object* v_usedLetOnly_1649_, lean_object* v_inst_1650_, lean_object* v_toBind_1651_, lean_object* v___f_1652_, lean_object* v_a_1653_){
_start:
{
uint8_t v_usedLetOnly_boxed_1654_; lean_object* v_res_1655_; 
v_usedLetOnly_boxed_1654_ = lean_unbox(v_usedLetOnly_1649_);
v_res_1655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1648_, v_usedLetOnly_boxed_1654_, v_inst_1650_, v_toBind_1651_, v___f_1652_, v_a_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1656_, uint8_t v_usedLetOnly_1657_, lean_object* v_inst_1658_, lean_object* v_toBind_1659_, lean_object* v___f_1660_, lean_object* v_a_1661_){
_start:
{
uint8_t v___x_1662_; uint8_t v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1662_ = 0;
v___x_1663_ = 1;
v___x_1664_ = 1;
v___x_1665_ = lean_box(v___x_1662_);
v___x_1666_ = lean_box(v_usedLetOnly_1657_);
v___x_1667_ = lean_box(v___x_1662_);
v___x_1668_ = lean_box(v___x_1663_);
v___x_1669_ = lean_box(v___x_1664_);
v___x_1670_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1670_, 0, v_fvars_1656_);
lean_closure_set(v___x_1670_, 1, v_a_1661_);
lean_closure_set(v___x_1670_, 2, v___x_1665_);
lean_closure_set(v___x_1670_, 3, v___x_1666_);
lean_closure_set(v___x_1670_, 4, v___x_1667_);
lean_closure_set(v___x_1670_, 5, v___x_1668_);
lean_closure_set(v___x_1670_, 6, v___x_1669_);
v___x_1671_ = lean_apply_2(v_inst_1658_, lean_box(0), v___x_1670_);
v___x_1672_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1671_, v___f_1660_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1673_, lean_object* v_usedLetOnly_1674_, lean_object* v_inst_1675_, lean_object* v_toBind_1676_, lean_object* v___f_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_usedLetOnly_boxed_1679_; lean_object* v_res_1680_; 
v_usedLetOnly_boxed_1679_ = lean_unbox(v_usedLetOnly_1674_);
v_res_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1673_, v_usedLetOnly_boxed_1679_, v_inst_1675_, v_toBind_1676_, v___f_1677_, v_a_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1681_, lean_object* v___x_1682_, lean_object* v_binderName_1683_, uint8_t v_binderInfo_1684_, lean_object* v___f_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v___x_1688_; lean_object* v___x_4102__overap_1689_; lean_object* v___x_1690_; 
v___x_1688_ = 0;
v___x_4102__overap_1689_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1681_, v___x_1682_, v_binderName_1683_, v_binderInfo_1684_, v_a_1687_, v___f_1685_, v___x_1688_);
v___x_1690_ = lean_apply_1(v___x_4102__overap_1689_, v_a_1686_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v_binderName_1693_, lean_object* v_binderInfo_1694_, lean_object* v___f_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
uint8_t v_binderInfo_4253__boxed_1698_; lean_object* v_res_1699_; 
v_binderInfo_4253__boxed_1698_ = lean_unbox(v_binderInfo_1694_);
v_res_1699_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1691_, v___x_1692_, v_binderName_1693_, v_binderInfo_4253__boxed_1698_, v___f_1695_, v_a_1696_, v_a_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1700_, uint8_t v_usedLetOnly_1701_, lean_object* v_inst_1702_, lean_object* v_toBind_1703_, lean_object* v___f_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v___x_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1706_ = 0;
v___x_1707_ = 1;
v___x_1708_ = 1;
v___x_1709_ = lean_box(v___x_1706_);
v___x_1710_ = lean_box(v_usedLetOnly_1701_);
v___x_1711_ = lean_box(v___x_1707_);
v___x_1712_ = lean_box(v___x_1708_);
v___x_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1713_, 0, v_fvars_1700_);
lean_closure_set(v___x_1713_, 1, v_a_1705_);
lean_closure_set(v___x_1713_, 2, v___x_1709_);
lean_closure_set(v___x_1713_, 3, v___x_1710_);
lean_closure_set(v___x_1713_, 4, v___x_1711_);
lean_closure_set(v___x_1713_, 5, v___x_1712_);
v___x_1714_ = lean_apply_2(v_inst_1702_, lean_box(0), v___x_1713_);
v___x_1715_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1714_, v___f_1704_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1716_, lean_object* v_usedLetOnly_1717_, lean_object* v_inst_1718_, lean_object* v_toBind_1719_, lean_object* v___f_1720_, lean_object* v_a_1721_){
_start:
{
uint8_t v_usedLetOnly_boxed_1722_; lean_object* v_res_1723_; 
v_usedLetOnly_boxed_1722_ = lean_unbox(v_usedLetOnly_1717_);
v_res_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1716_, v_usedLetOnly_boxed_1722_, v_inst_1718_, v_toBind_1719_, v___f_1720_, v_a_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1724_, lean_object* v___y_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_apply_2(v___f_1724_, v_a_1726_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1728_, lean_object* v_acc_1729_, lean_object* v_next_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_toPure_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_toPure_1732_ = lean_ctor_get(v_toApplicative_1728_, 1);
lean_inc(v_toPure_1732_);
lean_dec_ref(v_toApplicative_1728_);
v___x_1733_ = lean_array_fset(v_acc_1729_, v_next_1730_, v_a_1731_);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = lean_apply_2(v_toPure_1732_, lean_box(0), v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1736_, lean_object* v_acc_1737_, lean_object* v_next_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1736_, v_acc_1737_, v_next_1738_, v_a_1739_);
lean_dec(v_next_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1741_, lean_object* v_next_1742_, lean_object* v_G_1743_, lean_object* v___y_1744_, lean_object* v_a_1745_){
_start:
{
if (lean_obj_tag(v_a_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_toPure_1747_; lean_object* v___x_1748_; 
lean_dec(v___y_1744_);
lean_dec(v_G_1743_);
v_a_1746_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v_a_1745_);
v_toPure_1747_ = lean_ctor_get(v_toApplicative_1741_, 1);
lean_inc(v_toPure_1747_);
lean_dec_ref(v_toApplicative_1741_);
v___x_1748_ = lean_apply_2(v_toPure_1747_, lean_box(0), v_a_1746_);
return v___x_1748_;
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v_toApplicative_1741_);
v_a_1749_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v_a_1745_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_next_1742_, v___x_1750_);
v___x_1752_ = lean_apply_5(v_G_1743_, v___x_1751_, v_a_1749_, lean_box(0), lean_box(0), v___y_1744_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_1753_, lean_object* v_next_1754_, lean_object* v_G_1755_, lean_object* v___y_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_1753_, v_next_1754_, v_G_1755_, v___y_1756_, v_a_1757_);
lean_dec(v_next_1754_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_pre_1763_, lean_object* v_post_1764_, uint8_t v_usedLetOnly_1765_, uint8_t v_skipConstInApp_1766_, uint8_t v_skipInstances_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l_Lean_mkAppN(v_f_1759_, v_a_1771_);
v___x_1773_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_1760_, v_inst_1761_, v_inst_1762_, v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v_x_1768_, v_x_1769_, v___x_1772_, v___y_1770_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_pre_1778_, lean_object* v_post_1779_, lean_object* v_usedLetOnly_1780_, lean_object* v_skipConstInApp_1781_, lean_object* v_skipInstances_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v_a_1786_){
_start:
{
uint8_t v_usedLetOnly_boxed_1787_; uint8_t v_skipConstInApp_boxed_1788_; uint8_t v_skipInstances_boxed_1789_; lean_object* v_res_1790_; 
v_usedLetOnly_boxed_1787_ = lean_unbox(v_usedLetOnly_1780_);
v_skipConstInApp_boxed_1788_ = lean_unbox(v_skipConstInApp_1781_);
v_skipInstances_boxed_1789_ = lean_unbox(v_skipInstances_1782_);
v_res_1790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_1774_, v_inst_1775_, v_inst_1776_, v_inst_1777_, v_pre_1778_, v_post_1779_, v_usedLetOnly_boxed_1787_, v_skipConstInApp_boxed_1788_, v_skipInstances_boxed_1789_, v_x_1783_, v_x_1784_, v___y_1785_, v_a_1786_);
lean_dec_ref(v_a_1786_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_pre_1794_, lean_object* v_post_1795_, lean_object* v_usedLetOnly_1796_, lean_object* v_skipConstInApp_1797_, lean_object* v_skipInstances_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_e_1801_, lean_object* v_a_1802_){
_start:
{
uint8_t v_usedLetOnly_boxed_1803_; uint8_t v_skipConstInApp_boxed_1804_; uint8_t v_skipInstances_boxed_1805_; lean_object* v_res_1806_; 
v_usedLetOnly_boxed_1803_ = lean_unbox(v_usedLetOnly_1796_);
v_skipConstInApp_boxed_1804_ = lean_unbox(v_skipConstInApp_1797_);
v_skipInstances_boxed_1805_ = lean_unbox(v_skipInstances_1798_);
v_res_1806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1791_, v_inst_1792_, v_inst_1793_, v_pre_1794_, v_post_1795_, v_usedLetOnly_boxed_1803_, v_skipConstInApp_boxed_1804_, v_skipInstances_boxed_1805_, v_x_1799_, v_x_1800_, v_e_1801_, v_a_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_1807_, lean_object* v_toApplicative_1808_, lean_object* v_toBind_1809_, lean_object* v___f_1810_, lean_object* v_paramInfo_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_pre_1815_, lean_object* v_post_1816_, uint8_t v_usedLetOnly_1817_, uint8_t v_skipConstInApp_1818_, uint8_t v_skipInstances_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_next_1822_, lean_object* v_acc_1823_, lean_object* v_h_1824_, lean_object* v_G_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_nat_dec_lt(v_next_1822_, v___x_1807_);
if (v___x_1827_ == 0)
{
lean_object* v_toPure_1828_; lean_object* v___x_1829_; 
lean_dec(v___y_1826_);
lean_dec(v_G_1825_);
lean_dec(v_next_1822_);
lean_dec(v_x_1821_);
lean_dec(v_post_1816_);
lean_dec(v_pre_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec(v___f_1810_);
lean_dec(v_toBind_1809_);
v_toPure_1828_ = lean_ctor_get(v_toApplicative_1808_, 1);
lean_inc(v_toPure_1828_);
lean_dec_ref(v_toApplicative_1808_);
v___x_1829_ = lean_apply_2(v_toPure_1828_, lean_box(0), v_acc_1823_);
return v___x_1829_;
}
else
{
lean_object* v___f_1830_; lean_object* v___y_1832_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
lean_inc(v___y_1826_);
lean_inc(v_next_1822_);
lean_inc_ref(v_toApplicative_1808_);
v___f_1830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1830_, 0, v_toApplicative_1808_);
lean_closure_set(v___f_1830_, 1, v_next_1822_);
lean_closure_set(v___f_1830_, 2, v_G_1825_);
lean_closure_set(v___f_1830_, 3, v___y_1826_);
v___x_1835_ = lean_array_fget_borrowed(v_acc_1823_, v_next_1822_);
v___x_1836_ = lean_array_get_size(v_paramInfo_1811_);
v___x_1837_ = lean_nat_dec_lt(v_next_1822_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___f_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_inc(v___x_1835_);
v___f_1838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1838_, 0, v_toApplicative_1808_);
lean_closure_set(v___f_1838_, 1, v_acc_1823_);
lean_closure_set(v___f_1838_, 2, v_next_1822_);
v___x_1839_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1812_, v_inst_1813_, v_inst_1814_, v_pre_1815_, v_post_1816_, v_usedLetOnly_1817_, v_skipConstInApp_1818_, v_skipInstances_1819_, v_x_1820_, v_x_1821_, v___x_1835_, v___y_1826_);
lean_inc(v_toBind_1809_);
v___x_1840_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1839_, v___f_1838_);
v___y_1832_ = v___x_1840_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1841_; uint8_t v_isInstance_1842_; 
v___x_1841_ = lean_array_fget_borrowed(v_paramInfo_1811_, v_next_1822_);
v_isInstance_1842_ = lean_ctor_get_uint8(v___x_1841_, sizeof(void*)*1 + 4);
if (v_isInstance_1842_ == 0)
{
lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc(v___x_1835_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1843_, 0, v_toApplicative_1808_);
lean_closure_set(v___f_1843_, 1, v_acc_1823_);
lean_closure_set(v___f_1843_, 2, v_next_1822_);
v___x_1844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1812_, v_inst_1813_, v_inst_1814_, v_pre_1815_, v_post_1816_, v_usedLetOnly_1817_, v_skipConstInApp_1818_, v_skipInstances_1819_, v_x_1820_, v_x_1821_, v___x_1835_, v___y_1826_);
lean_inc(v_toBind_1809_);
v___x_1845_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1844_, v___f_1843_);
v___y_1832_ = v___x_1845_;
goto v___jp_1831_;
}
else
{
lean_object* v_toPure_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v___y_1826_);
lean_dec(v_next_1822_);
lean_dec(v_x_1821_);
lean_dec(v_post_1816_);
lean_dec(v_pre_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec(v_inst_1813_);
lean_dec_ref(v_inst_1812_);
v_toPure_1846_ = lean_ctor_get(v_toApplicative_1808_, 1);
lean_inc(v_toPure_1846_);
lean_dec_ref(v_toApplicative_1808_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_acc_1823_);
v___x_1848_ = lean_apply_2(v_toPure_1846_, lean_box(0), v___x_1847_);
v___y_1832_ = v___x_1848_;
goto v___jp_1831_;
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_inc(v_toBind_1809_);
v___x_1833_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___y_1832_, v___f_1810_);
v___x_1834_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1833_, v___f_1830_);
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_1849_ = _args[0];
lean_object* v_toApplicative_1850_ = _args[1];
lean_object* v_toBind_1851_ = _args[2];
lean_object* v___f_1852_ = _args[3];
lean_object* v_paramInfo_1853_ = _args[4];
lean_object* v_inst_1854_ = _args[5];
lean_object* v_inst_1855_ = _args[6];
lean_object* v_inst_1856_ = _args[7];
lean_object* v_pre_1857_ = _args[8];
lean_object* v_post_1858_ = _args[9];
lean_object* v_usedLetOnly_1859_ = _args[10];
lean_object* v_skipConstInApp_1860_ = _args[11];
lean_object* v_skipInstances_1861_ = _args[12];
lean_object* v_x_1862_ = _args[13];
lean_object* v_x_1863_ = _args[14];
lean_object* v_next_1864_ = _args[15];
lean_object* v_acc_1865_ = _args[16];
lean_object* v_h_1866_ = _args[17];
lean_object* v_G_1867_ = _args[18];
lean_object* v___y_1868_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_1869_; uint8_t v_skipConstInApp_boxed_1870_; uint8_t v_skipInstances_boxed_1871_; lean_object* v_res_1872_; 
v_usedLetOnly_boxed_1869_ = lean_unbox(v_usedLetOnly_1859_);
v_skipConstInApp_boxed_1870_ = lean_unbox(v_skipConstInApp_1860_);
v_skipInstances_boxed_1871_ = lean_unbox(v_skipInstances_1861_);
v_res_1872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_1849_, v_toApplicative_1850_, v_toBind_1851_, v___f_1852_, v_paramInfo_1853_, v_inst_1854_, v_inst_1855_, v_inst_1856_, v_pre_1857_, v_post_1858_, v_usedLetOnly_boxed_1869_, v_skipConstInApp_boxed_1870_, v_skipInstances_boxed_1871_, v_x_1862_, v_x_1863_, v_next_1864_, v_acc_1865_, v_h_1866_, v_G_1867_, v___y_1868_);
lean_dec_ref(v_paramInfo_1853_);
lean_dec(v___x_1849_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_1873_, lean_object* v_toApplicative_1874_, lean_object* v_toBind_1875_, lean_object* v___f_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_pre_1880_, lean_object* v_post_1881_, uint8_t v_usedLetOnly_1882_, uint8_t v_skipConstInApp_1883_, uint8_t v_skipInstances_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_args_1887_, lean_object* v___y_1888_, lean_object* v___f_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_paramInfo_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_3879__overap_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_paramInfo_1891_ = lean_ctor_get(v_a_1890_, 0);
lean_inc_ref(v_paramInfo_1891_);
lean_dec_ref(v_a_1890_);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_box(v_usedLetOnly_1882_);
v___x_1894_ = lean_box(v_skipConstInApp_1883_);
v___x_1895_ = lean_box(v_skipInstances_1884_);
lean_inc(v_toBind_1875_);
v___f_1896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_1896_, 0, v___x_1873_);
lean_closure_set(v___f_1896_, 1, v_toApplicative_1874_);
lean_closure_set(v___f_1896_, 2, v_toBind_1875_);
lean_closure_set(v___f_1896_, 3, v___f_1876_);
lean_closure_set(v___f_1896_, 4, v_paramInfo_1891_);
lean_closure_set(v___f_1896_, 5, v_inst_1877_);
lean_closure_set(v___f_1896_, 6, v_inst_1878_);
lean_closure_set(v___f_1896_, 7, v_inst_1879_);
lean_closure_set(v___f_1896_, 8, v_pre_1880_);
lean_closure_set(v___f_1896_, 9, v_post_1881_);
lean_closure_set(v___f_1896_, 10, v___x_1893_);
lean_closure_set(v___f_1896_, 11, v___x_1894_);
lean_closure_set(v___f_1896_, 12, v___x_1895_);
lean_closure_set(v___f_1896_, 13, v_x_1885_);
lean_closure_set(v___f_1896_, 14, v_x_1886_);
v___x_3879__overap_1897_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1896_, v___x_1892_, v_args_1887_, lean_box(0));
v___x_1898_ = lean_apply_1(v___x_3879__overap_1897_, v___y_1888_);
v___x_1899_ = lean_apply_4(v_toBind_1875_, lean_box(0), lean_box(0), v___x_1898_, v___f_1889_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_1900_ = _args[0];
lean_object* v_toApplicative_1901_ = _args[1];
lean_object* v_toBind_1902_ = _args[2];
lean_object* v___f_1903_ = _args[3];
lean_object* v_inst_1904_ = _args[4];
lean_object* v_inst_1905_ = _args[5];
lean_object* v_inst_1906_ = _args[6];
lean_object* v_pre_1907_ = _args[7];
lean_object* v_post_1908_ = _args[8];
lean_object* v_usedLetOnly_1909_ = _args[9];
lean_object* v_skipConstInApp_1910_ = _args[10];
lean_object* v_skipInstances_1911_ = _args[11];
lean_object* v_x_1912_ = _args[12];
lean_object* v_x_1913_ = _args[13];
lean_object* v_args_1914_ = _args[14];
lean_object* v___y_1915_ = _args[15];
lean_object* v___f_1916_ = _args[16];
lean_object* v_a_1917_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_1918_; uint8_t v_skipConstInApp_boxed_1919_; uint8_t v_skipInstances_boxed_1920_; lean_object* v_res_1921_; 
v_usedLetOnly_boxed_1918_ = lean_unbox(v_usedLetOnly_1909_);
v_skipConstInApp_boxed_1919_ = lean_unbox(v_skipConstInApp_1910_);
v_skipInstances_boxed_1920_ = lean_unbox(v_skipInstances_1911_);
v_res_1921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_1900_, v_toApplicative_1901_, v_toBind_1902_, v___f_1903_, v_inst_1904_, v_inst_1905_, v_inst_1906_, v_pre_1907_, v_post_1908_, v_usedLetOnly_boxed_1918_, v_skipConstInApp_boxed_1919_, v_skipInstances_boxed_1920_, v_x_1912_, v_x_1913_, v_args_1914_, v___y_1915_, v___f_1916_, v_a_1917_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_pre_1926_, lean_object* v_post_1927_, uint8_t v_usedLetOnly_1928_, uint8_t v_skipConstInApp_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_, lean_object* v_args_1932_, lean_object* v___x_1933_, lean_object* v_toBind_1934_, lean_object* v_toApplicative_1935_, lean_object* v___f_1936_, lean_object* v_f_1937_, lean_object* v___y_1938_){
_start:
{
if (v_skipInstances_1922_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; size_t v_sz_1947_; size_t v___x_1948_; lean_object* v___x_3892__overap_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v___f_1936_);
lean_dec_ref(v_toApplicative_1935_);
v___x_1939_ = lean_box(v_usedLetOnly_1928_);
v___x_1940_ = lean_box(v_skipConstInApp_1929_);
v___x_1941_ = lean_box(v_skipInstances_1922_);
lean_inc(v___y_1938_);
lean_inc(v_x_1931_);
lean_inc(v_post_1927_);
lean_inc(v_pre_1926_);
lean_inc_ref(v_inst_1925_);
lean_inc(v_inst_1924_);
lean_inc_ref(v_inst_1923_);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1942_, 0, v_f_1937_);
lean_closure_set(v___f_1942_, 1, v_inst_1923_);
lean_closure_set(v___f_1942_, 2, v_inst_1924_);
lean_closure_set(v___f_1942_, 3, v_inst_1925_);
lean_closure_set(v___f_1942_, 4, v_pre_1926_);
lean_closure_set(v___f_1942_, 5, v_post_1927_);
lean_closure_set(v___f_1942_, 6, v___x_1939_);
lean_closure_set(v___f_1942_, 7, v___x_1940_);
lean_closure_set(v___f_1942_, 8, v___x_1941_);
lean_closure_set(v___f_1942_, 9, v_x_1930_);
lean_closure_set(v___f_1942_, 10, v_x_1931_);
lean_closure_set(v___f_1942_, 11, v___y_1938_);
v___x_1943_ = lean_box(v_usedLetOnly_1928_);
v___x_1944_ = lean_box(v_skipConstInApp_1929_);
v___x_1945_ = lean_box(v_skipInstances_1922_);
v___x_1946_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_1946_, 0, v_inst_1923_);
lean_closure_set(v___x_1946_, 1, v_inst_1924_);
lean_closure_set(v___x_1946_, 2, v_inst_1925_);
lean_closure_set(v___x_1946_, 3, v_pre_1926_);
lean_closure_set(v___x_1946_, 4, v_post_1927_);
lean_closure_set(v___x_1946_, 5, v___x_1943_);
lean_closure_set(v___x_1946_, 6, v___x_1944_);
lean_closure_set(v___x_1946_, 7, v___x_1945_);
lean_closure_set(v___x_1946_, 8, v_x_1930_);
lean_closure_set(v___x_1946_, 9, v_x_1931_);
v_sz_1947_ = lean_array_size(v_args_1932_);
v___x_1948_ = ((size_t)0ULL);
v___x_3892__overap_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1933_, v___x_1946_, v_sz_1947_, v___x_1948_, v_args_1932_);
v___x_1950_ = lean_apply_1(v___x_3892__overap_1949_, v___y_1938_);
v___x_1951_ = lean_apply_4(v_toBind_1934_, lean_box(0), lean_box(0), v___x_1950_, v___f_1942_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___f_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v___x_1933_);
v___x_1952_ = lean_box(v_usedLetOnly_1928_);
v___x_1953_ = lean_box(v_skipConstInApp_1929_);
v___x_1954_ = lean_box(v_skipInstances_1922_);
lean_inc(v___y_1938_);
lean_inc(v_x_1931_);
lean_inc(v_post_1927_);
lean_inc(v_pre_1926_);
lean_inc_ref(v_inst_1925_);
lean_inc(v_inst_1924_);
lean_inc_ref(v_inst_1923_);
lean_inc_ref(v_f_1937_);
v___f_1955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1955_, 0, v_f_1937_);
lean_closure_set(v___f_1955_, 1, v_inst_1923_);
lean_closure_set(v___f_1955_, 2, v_inst_1924_);
lean_closure_set(v___f_1955_, 3, v_inst_1925_);
lean_closure_set(v___f_1955_, 4, v_pre_1926_);
lean_closure_set(v___f_1955_, 5, v_post_1927_);
lean_closure_set(v___f_1955_, 6, v___x_1952_);
lean_closure_set(v___f_1955_, 7, v___x_1953_);
lean_closure_set(v___f_1955_, 8, v___x_1954_);
lean_closure_set(v___f_1955_, 9, v_x_1930_);
lean_closure_set(v___f_1955_, 10, v_x_1931_);
lean_closure_set(v___f_1955_, 11, v___y_1938_);
v___x_1956_ = lean_array_get_size(v_args_1932_);
v___x_1957_ = lean_box(v_usedLetOnly_1928_);
v___x_1958_ = lean_box(v_skipConstInApp_1929_);
v___x_1959_ = lean_box(v_skipInstances_1922_);
lean_inc(v_inst_1924_);
lean_inc(v_toBind_1934_);
v___f_1960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_1960_, 0, v___x_1956_);
lean_closure_set(v___f_1960_, 1, v_toApplicative_1935_);
lean_closure_set(v___f_1960_, 2, v_toBind_1934_);
lean_closure_set(v___f_1960_, 3, v___f_1936_);
lean_closure_set(v___f_1960_, 4, v_inst_1923_);
lean_closure_set(v___f_1960_, 5, v_inst_1924_);
lean_closure_set(v___f_1960_, 6, v_inst_1925_);
lean_closure_set(v___f_1960_, 7, v_pre_1926_);
lean_closure_set(v___f_1960_, 8, v_post_1927_);
lean_closure_set(v___f_1960_, 9, v___x_1957_);
lean_closure_set(v___f_1960_, 10, v___x_1958_);
lean_closure_set(v___f_1960_, 11, v___x_1959_);
lean_closure_set(v___f_1960_, 12, v_x_1930_);
lean_closure_set(v___f_1960_, 13, v_x_1931_);
lean_closure_set(v___f_1960_, 14, v_args_1932_);
lean_closure_set(v___f_1960_, 15, v___y_1938_);
lean_closure_set(v___f_1960_, 16, v___f_1955_);
v___x_1961_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_1961_, 0, v_f_1937_);
lean_closure_set(v___x_1961_, 1, v___x_1956_);
v___x_1962_ = lean_apply_2(v_inst_1924_, lean_box(0), v___x_1961_);
v___x_1963_ = lean_apply_4(v_toBind_1934_, lean_box(0), lean_box(0), v___x_1962_, v___f_1960_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_1964_ = _args[0];
lean_object* v_inst_1965_ = _args[1];
lean_object* v_inst_1966_ = _args[2];
lean_object* v_inst_1967_ = _args[3];
lean_object* v_pre_1968_ = _args[4];
lean_object* v_post_1969_ = _args[5];
lean_object* v_usedLetOnly_1970_ = _args[6];
lean_object* v_skipConstInApp_1971_ = _args[7];
lean_object* v_x_1972_ = _args[8];
lean_object* v_x_1973_ = _args[9];
lean_object* v_args_1974_ = _args[10];
lean_object* v___x_1975_ = _args[11];
lean_object* v_toBind_1976_ = _args[12];
lean_object* v_toApplicative_1977_ = _args[13];
lean_object* v___f_1978_ = _args[14];
lean_object* v_f_1979_ = _args[15];
lean_object* v___y_1980_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_1981_; uint8_t v_usedLetOnly_boxed_1982_; uint8_t v_skipConstInApp_boxed_1983_; lean_object* v_res_1984_; 
v_skipInstances_boxed_1981_ = lean_unbox(v_skipInstances_1964_);
v_usedLetOnly_boxed_1982_ = lean_unbox(v_usedLetOnly_1970_);
v_skipConstInApp_boxed_1983_ = lean_unbox(v_skipConstInApp_1971_);
v_res_1984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_1981_, v_inst_1965_, v_inst_1966_, v_inst_1967_, v_pre_1968_, v_post_1969_, v_usedLetOnly_boxed_1982_, v_skipConstInApp_boxed_1983_, v_x_1972_, v_x_1973_, v_args_1974_, v___x_1975_, v_toBind_1976_, v_toApplicative_1977_, v___f_1978_, v_f_1979_, v___y_1980_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_pre_1989_, lean_object* v_post_1990_, uint8_t v_usedLetOnly_1991_, uint8_t v_skipConstInApp_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v___x_1995_, lean_object* v_toBind_1996_, lean_object* v_toApplicative_1997_, lean_object* v___f_1998_, lean_object* v_f_1999_, lean_object* v_args_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___f_2005_; lean_object* v___f_2006_; 
v___x_2002_ = lean_box(v_skipInstances_1985_);
v___x_2003_ = lean_box(v_usedLetOnly_1991_);
v___x_2004_ = lean_box(v_skipConstInApp_1992_);
lean_inc_ref(v_toApplicative_1997_);
lean_inc(v_toBind_1996_);
lean_inc(v_x_1994_);
lean_inc(v_post_1990_);
lean_inc(v_pre_1989_);
lean_inc_ref(v_inst_1988_);
lean_inc(v_inst_1987_);
lean_inc_ref(v_inst_1986_);
v___f_2005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2005_, 0, v___x_2002_);
lean_closure_set(v___f_2005_, 1, v_inst_1986_);
lean_closure_set(v___f_2005_, 2, v_inst_1987_);
lean_closure_set(v___f_2005_, 3, v_inst_1988_);
lean_closure_set(v___f_2005_, 4, v_pre_1989_);
lean_closure_set(v___f_2005_, 5, v_post_1990_);
lean_closure_set(v___f_2005_, 6, v___x_2003_);
lean_closure_set(v___f_2005_, 7, v___x_2004_);
lean_closure_set(v___f_2005_, 8, v_x_1993_);
lean_closure_set(v___f_2005_, 9, v_x_1994_);
lean_closure_set(v___f_2005_, 10, v_args_2000_);
lean_closure_set(v___f_2005_, 11, v___x_1995_);
lean_closure_set(v___f_2005_, 12, v_toBind_1996_);
lean_closure_set(v___f_2005_, 13, v_toApplicative_1997_);
lean_closure_set(v___f_2005_, 14, v___f_1998_);
lean_inc(v___y_2001_);
v___f_2006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7), 3, 2);
lean_closure_set(v___f_2006_, 0, v___f_2005_);
lean_closure_set(v___f_2006_, 1, v___y_2001_);
if (v_skipConstInApp_1992_ == 0)
{
lean_dec_ref(v_toApplicative_1997_);
goto v___jp_2007_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Expr_isConst(v_f_1999_);
if (v___x_2010_ == 0)
{
lean_dec_ref(v_toApplicative_1997_);
goto v___jp_2007_;
}
else
{
lean_object* v_toPure_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v___y_2001_);
lean_dec(v_x_1994_);
lean_dec(v_post_1990_);
lean_dec(v_pre_1989_);
lean_dec_ref(v_inst_1988_);
lean_dec(v_inst_1987_);
lean_dec_ref(v_inst_1986_);
v_toPure_2011_ = lean_ctor_get(v_toApplicative_1997_, 1);
lean_inc(v_toPure_2011_);
lean_dec_ref(v_toApplicative_1997_);
v___x_2012_ = lean_apply_2(v_toPure_2011_, lean_box(0), v_f_1999_);
v___x_2013_ = lean_apply_4(v_toBind_1996_, lean_box(0), lean_box(0), v___x_2012_, v___f_2006_);
return v___x_2013_;
}
}
v___jp_2007_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_1986_, v_inst_1987_, v_inst_1988_, v_pre_1989_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1985_, v_x_1993_, v_x_1994_, v_f_1999_, v___y_2001_);
v___x_2009_ = lean_apply_4(v_toBind_1996_, lean_box(0), lean_box(0), v___x_2008_, v___f_2006_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2014_ = _args[0];
lean_object* v_inst_2015_ = _args[1];
lean_object* v_inst_2016_ = _args[2];
lean_object* v_inst_2017_ = _args[3];
lean_object* v_pre_2018_ = _args[4];
lean_object* v_post_2019_ = _args[5];
lean_object* v_usedLetOnly_2020_ = _args[6];
lean_object* v_skipConstInApp_2021_ = _args[7];
lean_object* v_x_2022_ = _args[8];
lean_object* v_x_2023_ = _args[9];
lean_object* v___x_2024_ = _args[10];
lean_object* v_toBind_2025_ = _args[11];
lean_object* v_toApplicative_2026_ = _args[12];
lean_object* v___f_2027_ = _args[13];
lean_object* v_f_2028_ = _args[14];
lean_object* v_args_2029_ = _args[15];
lean_object* v___y_2030_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2031_; uint8_t v_usedLetOnly_boxed_2032_; uint8_t v_skipConstInApp_boxed_2033_; lean_object* v_res_2034_; 
v_skipInstances_boxed_2031_ = lean_unbox(v_skipInstances_2014_);
v_usedLetOnly_boxed_2032_ = lean_unbox(v_usedLetOnly_2020_);
v_skipConstInApp_boxed_2033_ = lean_unbox(v_skipConstInApp_2021_);
v_res_2034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2031_, v_inst_2015_, v_inst_2016_, v_inst_2017_, v_pre_2018_, v_post_2019_, v_usedLetOnly_boxed_2032_, v_skipConstInApp_boxed_2033_, v_x_2022_, v_x_2023_, v___x_2024_, v_toBind_2025_, v_toApplicative_2026_, v___f_2027_, v_f_2028_, v_args_2029_, v___y_2030_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_pre_2041_, lean_object* v_post_2042_, uint8_t v_usedLetOnly_2043_, uint8_t v_skipConstInApp_2044_, uint8_t v_skipInstances_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_body_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_array_push(v_fvars_2037_, v_x_2049_);
v___x_2052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_, v_pre_2041_, v_post_2042_, v_usedLetOnly_2043_, v_skipConstInApp_2044_, v_skipInstances_2045_, v_x_2046_, v_x_2047_, v___x_2051_, v_body_2048_, v___y_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2053_, lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_pre_2057_, lean_object* v_post_2058_, lean_object* v_usedLetOnly_2059_, lean_object* v_skipConstInApp_2060_, lean_object* v_skipInstances_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_body_2064_, lean_object* v_x_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v_usedLetOnly_boxed_2067_; uint8_t v_skipConstInApp_boxed_2068_; uint8_t v_skipInstances_boxed_2069_; lean_object* v_res_2070_; 
v_usedLetOnly_boxed_2067_ = lean_unbox(v_usedLetOnly_2059_);
v_skipConstInApp_boxed_2068_ = lean_unbox(v_skipConstInApp_2060_);
v_skipInstances_boxed_2069_ = lean_unbox(v_skipInstances_2061_);
v_res_2070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2053_, v_inst_2054_, v_inst_2055_, v_inst_2056_, v_pre_2057_, v_post_2058_, v_usedLetOnly_boxed_2067_, v_skipConstInApp_boxed_2068_, v_skipInstances_boxed_2069_, v_x_2062_, v_x_2063_, v_body_2064_, v_x_2065_, v___y_2066_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_pre_2074_, lean_object* v_post_2075_, lean_object* v_usedLetOnly_2076_, lean_object* v_skipConstInApp_2077_, lean_object* v_skipInstances_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
uint8_t v_usedLetOnly_boxed_2083_; uint8_t v_skipConstInApp_boxed_2084_; uint8_t v_skipInstances_boxed_2085_; lean_object* v_res_2086_; 
v_usedLetOnly_boxed_2083_ = lean_unbox(v_usedLetOnly_2076_);
v_skipConstInApp_boxed_2084_ = lean_unbox(v_skipConstInApp_2077_);
v_skipInstances_boxed_2085_ = lean_unbox(v_skipInstances_2078_);
v_res_2086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2071_, v_inst_2072_, v_inst_2073_, v_pre_2074_, v_post_2075_, v_usedLetOnly_boxed_2083_, v_skipConstInApp_boxed_2084_, v_skipInstances_boxed_2085_, v_x_2079_, v_x_2080_, v_a_2081_, v_a_2082_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_pre_2090_, lean_object* v_post_2091_, uint8_t v_usedLetOnly_2092_, uint8_t v_skipConstInApp_2093_, uint8_t v_skipInstances_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_fvars_2097_, lean_object* v_e_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; 
lean_inc_ref(v_inst_2087_);
v___x_2100_ = l_ReaderT_instMonad___redArg(v_inst_2087_);
v___x_2101_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0);
lean_inc_ref(v_inst_2089_);
v___f_2102_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2102_, 0, v___x_2101_);
lean_closure_set(v___f_2102_, 1, v_inst_2089_);
lean_inc_ref(v_inst_2089_);
v___f_2103_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2103_, 0, v___x_2101_);
lean_closure_set(v___f_2103_, 1, v_inst_2089_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___f_2102_);
lean_ctor_set(v___x_2104_, 1, v___f_2103_);
if (lean_obj_tag(v_e_2098_) == 7)
{
lean_object* v_binderName_2105_; lean_object* v_binderType_2106_; lean_object* v_body_2107_; uint8_t v_binderInfo_2108_; lean_object* v_toBind_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_binderName_2105_ = lean_ctor_get(v_e_2098_, 0);
lean_inc(v_binderName_2105_);
v_binderType_2106_ = lean_ctor_get(v_e_2098_, 1);
lean_inc_ref(v_binderType_2106_);
v_body_2107_ = lean_ctor_get(v_e_2098_, 2);
lean_inc_ref(v_body_2107_);
v_binderInfo_2108_ = lean_ctor_get_uint8(v_e_2098_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2098_);
v_toBind_2109_ = lean_ctor_get(v_inst_2087_, 1);
lean_inc(v_toBind_2109_);
v___x_2110_ = lean_box(v_usedLetOnly_2092_);
v___x_2111_ = lean_box(v_skipConstInApp_2093_);
v___x_2112_ = lean_box(v_skipInstances_2094_);
lean_inc(v_x_2096_);
lean_inc(v_post_2091_);
lean_inc(v_pre_2090_);
lean_inc_ref(v_inst_2089_);
lean_inc(v_inst_2088_);
lean_inc_ref(v_inst_2087_);
lean_inc_ref(v_fvars_2097_);
v___f_2113_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2113_, 0, v_fvars_2097_);
lean_closure_set(v___f_2113_, 1, v_inst_2087_);
lean_closure_set(v___f_2113_, 2, v_inst_2088_);
lean_closure_set(v___f_2113_, 3, v_inst_2089_);
lean_closure_set(v___f_2113_, 4, v_pre_2090_);
lean_closure_set(v___f_2113_, 5, v_post_2091_);
lean_closure_set(v___f_2113_, 6, v___x_2110_);
lean_closure_set(v___f_2113_, 7, v___x_2111_);
lean_closure_set(v___f_2113_, 8, v___x_2112_);
lean_closure_set(v___f_2113_, 9, v_x_2095_);
lean_closure_set(v___f_2113_, 10, v_x_2096_);
lean_closure_set(v___f_2113_, 11, v_body_2107_);
v___x_2114_ = lean_box(v_binderInfo_2108_);
lean_inc(v_a_2099_);
v___f_2115_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2115_, 0, v___x_2104_);
lean_closure_set(v___f_2115_, 1, v___x_2100_);
lean_closure_set(v___f_2115_, 2, v_binderName_2105_);
lean_closure_set(v___f_2115_, 3, v___x_2114_);
lean_closure_set(v___f_2115_, 4, v___f_2113_);
lean_closure_set(v___f_2115_, 5, v_a_2099_);
v___x_2116_ = lean_expr_instantiate_rev(v_binderType_2106_, v_fvars_2097_);
lean_dec_ref(v_fvars_2097_);
lean_dec_ref(v_binderType_2106_);
v___x_2117_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2087_, v_inst_2088_, v_inst_2089_, v_pre_2090_, v_post_2091_, v_usedLetOnly_2092_, v_skipConstInApp_2093_, v_skipInstances_2094_, v_x_2095_, v_x_2096_, v___x_2116_, v_a_2099_);
v___x_2118_ = lean_apply_4(v_toBind_2109_, lean_box(0), lean_box(0), v___x_2117_, v___f_2115_);
return v___x_2118_;
}
else
{
lean_object* v_toBind_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v___x_2104_);
lean_dec_ref(v___x_2100_);
v_toBind_2119_ = lean_ctor_get(v_inst_2087_, 1);
lean_inc(v_toBind_2119_);
v___x_2120_ = lean_box(v_usedLetOnly_2092_);
v___x_2121_ = lean_box(v_skipConstInApp_2093_);
v___x_2122_ = lean_box(v_skipInstances_2094_);
lean_inc(v_a_2099_);
lean_inc(v_x_2096_);
lean_inc(v_post_2091_);
lean_inc(v_pre_2090_);
lean_inc_ref(v_inst_2089_);
lean_inc(v_inst_2088_);
lean_inc_ref(v_inst_2087_);
v___f_2123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2123_, 0, v_inst_2087_);
lean_closure_set(v___f_2123_, 1, v_inst_2088_);
lean_closure_set(v___f_2123_, 2, v_inst_2089_);
lean_closure_set(v___f_2123_, 3, v_pre_2090_);
lean_closure_set(v___f_2123_, 4, v_post_2091_);
lean_closure_set(v___f_2123_, 5, v___x_2120_);
lean_closure_set(v___f_2123_, 6, v___x_2121_);
lean_closure_set(v___f_2123_, 7, v___x_2122_);
lean_closure_set(v___f_2123_, 8, v_x_2095_);
lean_closure_set(v___f_2123_, 9, v_x_2096_);
lean_closure_set(v___f_2123_, 10, v_a_2099_);
v___x_2124_ = lean_box(v_usedLetOnly_2092_);
lean_inc(v_toBind_2119_);
lean_inc(v_inst_2088_);
lean_inc_ref(v_fvars_2097_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2125_, 0, v_fvars_2097_);
lean_closure_set(v___f_2125_, 1, v___x_2124_);
lean_closure_set(v___f_2125_, 2, v_inst_2088_);
lean_closure_set(v___f_2125_, 3, v_toBind_2119_);
lean_closure_set(v___f_2125_, 4, v___f_2123_);
v___x_2126_ = lean_expr_instantiate_rev(v_e_2098_, v_fvars_2097_);
lean_dec_ref(v_fvars_2097_);
lean_dec_ref(v_e_2098_);
v___x_2127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2087_, v_inst_2088_, v_inst_2089_, v_pre_2090_, v_post_2091_, v_usedLetOnly_2092_, v_skipConstInApp_2093_, v_skipInstances_2094_, v_x_2095_, v_x_2096_, v___x_2126_, v_a_2099_);
v___x_2128_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v___x_2127_, v___f_2125_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_pre_2133_, lean_object* v_post_2134_, uint8_t v_usedLetOnly_2135_, uint8_t v_skipConstInApp_2136_, uint8_t v_skipInstances_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_body_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_array_push(v_fvars_2129_, v_x_2141_);
v___x_2144_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2130_, v_inst_2131_, v_inst_2132_, v_pre_2133_, v_post_2134_, v_usedLetOnly_2135_, v_skipConstInApp_2136_, v_skipInstances_2137_, v_x_2138_, v_x_2139_, v___x_2143_, v_body_2140_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_pre_2149_, lean_object* v_post_2150_, lean_object* v_usedLetOnly_2151_, lean_object* v_skipConstInApp_2152_, lean_object* v_skipInstances_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_body_2156_, lean_object* v_x_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_usedLetOnly_boxed_2159_; uint8_t v_skipConstInApp_boxed_2160_; uint8_t v_skipInstances_boxed_2161_; lean_object* v_res_2162_; 
v_usedLetOnly_boxed_2159_ = lean_unbox(v_usedLetOnly_2151_);
v_skipConstInApp_boxed_2160_ = lean_unbox(v_skipConstInApp_2152_);
v_skipInstances_boxed_2161_ = lean_unbox(v_skipInstances_2153_);
v_res_2162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2145_, v_inst_2146_, v_inst_2147_, v_inst_2148_, v_pre_2149_, v_post_2150_, v_usedLetOnly_boxed_2159_, v_skipConstInApp_boxed_2160_, v_skipInstances_boxed_2161_, v_x_2154_, v_x_2155_, v_body_2156_, v_x_2157_, v___y_2158_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_pre_2166_, lean_object* v_post_2167_, uint8_t v_usedLetOnly_2168_, uint8_t v_skipConstInApp_2169_, uint8_t v_skipInstances_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_fvars_2173_, lean_object* v_e_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
lean_inc_ref(v_inst_2163_);
v___x_2176_ = l_ReaderT_instMonad___redArg(v_inst_2163_);
v___x_2177_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0);
lean_inc_ref(v_inst_2165_);
v___f_2178_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2178_, 0, v___x_2177_);
lean_closure_set(v___f_2178_, 1, v_inst_2165_);
lean_inc_ref(v_inst_2165_);
v___f_2179_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2179_, 0, v___x_2177_);
lean_closure_set(v___f_2179_, 1, v_inst_2165_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___f_2178_);
lean_ctor_set(v___x_2180_, 1, v___f_2179_);
if (lean_obj_tag(v_e_2174_) == 6)
{
lean_object* v_binderName_2181_; lean_object* v_binderType_2182_; lean_object* v_body_2183_; uint8_t v_binderInfo_2184_; lean_object* v_toBind_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_binderName_2181_ = lean_ctor_get(v_e_2174_, 0);
lean_inc(v_binderName_2181_);
v_binderType_2182_ = lean_ctor_get(v_e_2174_, 1);
lean_inc_ref(v_binderType_2182_);
v_body_2183_ = lean_ctor_get(v_e_2174_, 2);
lean_inc_ref(v_body_2183_);
v_binderInfo_2184_ = lean_ctor_get_uint8(v_e_2174_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2174_);
v_toBind_2185_ = lean_ctor_get(v_inst_2163_, 1);
lean_inc(v_toBind_2185_);
v___x_2186_ = lean_box(v_usedLetOnly_2168_);
v___x_2187_ = lean_box(v_skipConstInApp_2169_);
v___x_2188_ = lean_box(v_skipInstances_2170_);
lean_inc(v_x_2172_);
lean_inc(v_post_2167_);
lean_inc(v_pre_2166_);
lean_inc_ref(v_inst_2165_);
lean_inc(v_inst_2164_);
lean_inc_ref(v_inst_2163_);
lean_inc_ref(v_fvars_2173_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2189_, 0, v_fvars_2173_);
lean_closure_set(v___f_2189_, 1, v_inst_2163_);
lean_closure_set(v___f_2189_, 2, v_inst_2164_);
lean_closure_set(v___f_2189_, 3, v_inst_2165_);
lean_closure_set(v___f_2189_, 4, v_pre_2166_);
lean_closure_set(v___f_2189_, 5, v_post_2167_);
lean_closure_set(v___f_2189_, 6, v___x_2186_);
lean_closure_set(v___f_2189_, 7, v___x_2187_);
lean_closure_set(v___f_2189_, 8, v___x_2188_);
lean_closure_set(v___f_2189_, 9, v_x_2171_);
lean_closure_set(v___f_2189_, 10, v_x_2172_);
lean_closure_set(v___f_2189_, 11, v_body_2183_);
v___x_2190_ = lean_box(v_binderInfo_2184_);
lean_inc(v_a_2175_);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2191_, 0, v___x_2180_);
lean_closure_set(v___f_2191_, 1, v___x_2176_);
lean_closure_set(v___f_2191_, 2, v_binderName_2181_);
lean_closure_set(v___f_2191_, 3, v___x_2190_);
lean_closure_set(v___f_2191_, 4, v___f_2189_);
lean_closure_set(v___f_2191_, 5, v_a_2175_);
v___x_2192_ = lean_expr_instantiate_rev(v_binderType_2182_, v_fvars_2173_);
lean_dec_ref(v_fvars_2173_);
lean_dec_ref(v_binderType_2182_);
v___x_2193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2163_, v_inst_2164_, v_inst_2165_, v_pre_2166_, v_post_2167_, v_usedLetOnly_2168_, v_skipConstInApp_2169_, v_skipInstances_2170_, v_x_2171_, v_x_2172_, v___x_2192_, v_a_2175_);
v___x_2194_ = lean_apply_4(v_toBind_2185_, lean_box(0), lean_box(0), v___x_2193_, v___f_2191_);
return v___x_2194_;
}
else
{
lean_object* v_toBind_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v___x_2180_);
lean_dec_ref(v___x_2176_);
v_toBind_2195_ = lean_ctor_get(v_inst_2163_, 1);
lean_inc(v_toBind_2195_);
v___x_2196_ = lean_box(v_usedLetOnly_2168_);
v___x_2197_ = lean_box(v_skipConstInApp_2169_);
v___x_2198_ = lean_box(v_skipInstances_2170_);
lean_inc(v_a_2175_);
lean_inc(v_x_2172_);
lean_inc(v_post_2167_);
lean_inc(v_pre_2166_);
lean_inc_ref(v_inst_2165_);
lean_inc(v_inst_2164_);
lean_inc_ref(v_inst_2163_);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2199_, 0, v_inst_2163_);
lean_closure_set(v___f_2199_, 1, v_inst_2164_);
lean_closure_set(v___f_2199_, 2, v_inst_2165_);
lean_closure_set(v___f_2199_, 3, v_pre_2166_);
lean_closure_set(v___f_2199_, 4, v_post_2167_);
lean_closure_set(v___f_2199_, 5, v___x_2196_);
lean_closure_set(v___f_2199_, 6, v___x_2197_);
lean_closure_set(v___f_2199_, 7, v___x_2198_);
lean_closure_set(v___f_2199_, 8, v_x_2171_);
lean_closure_set(v___f_2199_, 9, v_x_2172_);
lean_closure_set(v___f_2199_, 10, v_a_2175_);
v___x_2200_ = lean_box(v_usedLetOnly_2168_);
lean_inc(v_toBind_2195_);
lean_inc(v_inst_2164_);
lean_inc_ref(v_fvars_2173_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2201_, 0, v_fvars_2173_);
lean_closure_set(v___f_2201_, 1, v___x_2200_);
lean_closure_set(v___f_2201_, 2, v_inst_2164_);
lean_closure_set(v___f_2201_, 3, v_toBind_2195_);
lean_closure_set(v___f_2201_, 4, v___f_2199_);
v___x_2202_ = lean_expr_instantiate_rev(v_e_2174_, v_fvars_2173_);
lean_dec_ref(v_fvars_2173_);
lean_dec_ref(v_e_2174_);
v___x_2203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2163_, v_inst_2164_, v_inst_2165_, v_pre_2166_, v_post_2167_, v_usedLetOnly_2168_, v_skipConstInApp_2169_, v_skipInstances_2170_, v_x_2171_, v_x_2172_, v___x_2202_, v_a_2175_);
v___x_2204_ = lean_apply_4(v_toBind_2195_, lean_box(0), lean_box(0), v___x_2203_, v___f_2201_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_pre_2209_, lean_object* v_post_2210_, uint8_t v_usedLetOnly_2211_, uint8_t v_skipConstInApp_2212_, uint8_t v_skipInstances_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_body_2216_, lean_object* v_x_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_array_push(v_fvars_2205_, v_x_2217_);
v___x_2220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2206_, v_inst_2207_, v_inst_2208_, v_pre_2209_, v_post_2210_, v_usedLetOnly_2211_, v_skipConstInApp_2212_, v_skipInstances_2213_, v_x_2214_, v_x_2215_, v___x_2219_, v_body_2216_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_pre_2225_, lean_object* v_post_2226_, lean_object* v_usedLetOnly_2227_, lean_object* v_skipConstInApp_2228_, lean_object* v_skipInstances_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v_body_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_){
_start:
{
uint8_t v_usedLetOnly_boxed_2235_; uint8_t v_skipConstInApp_boxed_2236_; uint8_t v_skipInstances_boxed_2237_; lean_object* v_res_2238_; 
v_usedLetOnly_boxed_2235_ = lean_unbox(v_usedLetOnly_2227_);
v_skipConstInApp_boxed_2236_ = lean_unbox(v_skipConstInApp_2228_);
v_skipInstances_boxed_2237_ = lean_unbox(v_skipInstances_2229_);
v_res_2238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2221_, v_inst_2222_, v_inst_2223_, v_inst_2224_, v_pre_2225_, v_post_2226_, v_usedLetOnly_boxed_2235_, v_skipConstInApp_boxed_2236_, v_skipInstances_boxed_2237_, v_x_2230_, v_x_2231_, v_body_2232_, v_x_2233_, v___y_2234_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v_declName_2241_, lean_object* v___f_2242_, uint8_t v_nondep_2243_, lean_object* v_a_2244_, lean_object* v_value_2245_, lean_object* v_fvars_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_pre_2250_, lean_object* v_post_2251_, uint8_t v_usedLetOnly_2252_, uint8_t v_skipConstInApp_2253_, uint8_t v_skipInstances_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v_toBind_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2259_ = lean_box(v_nondep_2243_);
lean_inc(v_a_2244_);
v___f_2260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2260_, 0, v___x_2239_);
lean_closure_set(v___f_2260_, 1, v___x_2240_);
lean_closure_set(v___f_2260_, 2, v_declName_2241_);
lean_closure_set(v___f_2260_, 3, v_a_2258_);
lean_closure_set(v___f_2260_, 4, v___f_2242_);
lean_closure_set(v___f_2260_, 5, v___x_2259_);
lean_closure_set(v___f_2260_, 6, v_a_2244_);
v___x_2261_ = lean_expr_instantiate_rev(v_value_2245_, v_fvars_2246_);
v___x_2262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2247_, v_inst_2248_, v_inst_2249_, v_pre_2250_, v_post_2251_, v_usedLetOnly_2252_, v_skipConstInApp_2253_, v_skipInstances_2254_, v_x_2255_, v_x_2256_, v___x_2261_, v_a_2244_);
v___x_2263_ = lean_apply_4(v_toBind_2257_, lean_box(0), lean_box(0), v___x_2262_, v___f_2260_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2264_ = _args[0];
lean_object* v___x_2265_ = _args[1];
lean_object* v_declName_2266_ = _args[2];
lean_object* v___f_2267_ = _args[3];
lean_object* v_nondep_2268_ = _args[4];
lean_object* v_a_2269_ = _args[5];
lean_object* v_value_2270_ = _args[6];
lean_object* v_fvars_2271_ = _args[7];
lean_object* v_inst_2272_ = _args[8];
lean_object* v_inst_2273_ = _args[9];
lean_object* v_inst_2274_ = _args[10];
lean_object* v_pre_2275_ = _args[11];
lean_object* v_post_2276_ = _args[12];
lean_object* v_usedLetOnly_2277_ = _args[13];
lean_object* v_skipConstInApp_2278_ = _args[14];
lean_object* v_skipInstances_2279_ = _args[15];
lean_object* v_x_2280_ = _args[16];
lean_object* v_x_2281_ = _args[17];
lean_object* v_toBind_2282_ = _args[18];
lean_object* v_a_2283_ = _args[19];
_start:
{
uint8_t v_nondep_4384__boxed_2284_; uint8_t v_usedLetOnly_boxed_2285_; uint8_t v_skipConstInApp_boxed_2286_; uint8_t v_skipInstances_boxed_2287_; lean_object* v_res_2288_; 
v_nondep_4384__boxed_2284_ = lean_unbox(v_nondep_2268_);
v_usedLetOnly_boxed_2285_ = lean_unbox(v_usedLetOnly_2277_);
v_skipConstInApp_boxed_2286_ = lean_unbox(v_skipConstInApp_2278_);
v_skipInstances_boxed_2287_ = lean_unbox(v_skipInstances_2279_);
v_res_2288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2264_, v___x_2265_, v_declName_2266_, v___f_2267_, v_nondep_4384__boxed_2284_, v_a_2269_, v_value_2270_, v_fvars_2271_, v_inst_2272_, v_inst_2273_, v_inst_2274_, v_pre_2275_, v_post_2276_, v_usedLetOnly_boxed_2285_, v_skipConstInApp_boxed_2286_, v_skipInstances_boxed_2287_, v_x_2280_, v_x_2281_, v_toBind_2282_, v_a_2283_);
lean_dec_ref(v_fvars_2271_);
lean_dec_ref(v_value_2270_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_pre_2292_, lean_object* v_post_2293_, uint8_t v_usedLetOnly_2294_, uint8_t v_skipConstInApp_2295_, uint8_t v_skipInstances_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_, lean_object* v_fvars_2299_, lean_object* v_e_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; 
lean_inc_ref(v_inst_2289_);
v___x_2302_ = l_ReaderT_instMonad___redArg(v_inst_2289_);
v___x_2303_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0);
lean_inc_ref(v_inst_2291_);
v___f_2304_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2304_, 0, v___x_2303_);
lean_closure_set(v___f_2304_, 1, v_inst_2291_);
lean_inc_ref(v_inst_2291_);
v___f_2305_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2305_, 0, v___x_2303_);
lean_closure_set(v___f_2305_, 1, v_inst_2291_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___f_2304_);
lean_ctor_set(v___x_2306_, 1, v___f_2305_);
if (lean_obj_tag(v_e_2300_) == 8)
{
lean_object* v_declName_2307_; lean_object* v_type_2308_; lean_object* v_value_2309_; lean_object* v_body_2310_; uint8_t v_nondep_2311_; lean_object* v_toBind_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___f_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_declName_2307_ = lean_ctor_get(v_e_2300_, 0);
lean_inc(v_declName_2307_);
v_type_2308_ = lean_ctor_get(v_e_2300_, 1);
lean_inc_ref(v_type_2308_);
v_value_2309_ = lean_ctor_get(v_e_2300_, 2);
lean_inc_ref(v_value_2309_);
v_body_2310_ = lean_ctor_get(v_e_2300_, 3);
lean_inc_ref(v_body_2310_);
v_nondep_2311_ = lean_ctor_get_uint8(v_e_2300_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2300_);
v_toBind_2312_ = lean_ctor_get(v_inst_2289_, 1);
lean_inc(v_toBind_2312_);
v___x_2313_ = lean_box(v_usedLetOnly_2294_);
v___x_2314_ = lean_box(v_skipConstInApp_2295_);
v___x_2315_ = lean_box(v_skipInstances_2296_);
lean_inc(v_x_2298_);
lean_inc(v_post_2293_);
lean_inc(v_pre_2292_);
lean_inc_ref(v_inst_2291_);
lean_inc(v_inst_2290_);
lean_inc_ref(v_inst_2289_);
lean_inc_ref(v_fvars_2299_);
v___f_2316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2316_, 0, v_fvars_2299_);
lean_closure_set(v___f_2316_, 1, v_inst_2289_);
lean_closure_set(v___f_2316_, 2, v_inst_2290_);
lean_closure_set(v___f_2316_, 3, v_inst_2291_);
lean_closure_set(v___f_2316_, 4, v_pre_2292_);
lean_closure_set(v___f_2316_, 5, v_post_2293_);
lean_closure_set(v___f_2316_, 6, v___x_2313_);
lean_closure_set(v___f_2316_, 7, v___x_2314_);
lean_closure_set(v___f_2316_, 8, v___x_2315_);
lean_closure_set(v___f_2316_, 9, v_x_2297_);
lean_closure_set(v___f_2316_, 10, v_x_2298_);
lean_closure_set(v___f_2316_, 11, v_body_2310_);
v___x_2317_ = lean_box(v_nondep_2311_);
v___x_2318_ = lean_box(v_usedLetOnly_2294_);
v___x_2319_ = lean_box(v_skipConstInApp_2295_);
v___x_2320_ = lean_box(v_skipInstances_2296_);
lean_inc(v_toBind_2312_);
lean_inc(v_x_2298_);
lean_inc(v_post_2293_);
lean_inc(v_pre_2292_);
lean_inc_ref(v_inst_2291_);
lean_inc(v_inst_2290_);
lean_inc_ref(v_inst_2289_);
lean_inc_ref(v_fvars_2299_);
lean_inc(v_a_2301_);
v___f_2321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2321_, 0, v___x_2306_);
lean_closure_set(v___f_2321_, 1, v___x_2302_);
lean_closure_set(v___f_2321_, 2, v_declName_2307_);
lean_closure_set(v___f_2321_, 3, v___f_2316_);
lean_closure_set(v___f_2321_, 4, v___x_2317_);
lean_closure_set(v___f_2321_, 5, v_a_2301_);
lean_closure_set(v___f_2321_, 6, v_value_2309_);
lean_closure_set(v___f_2321_, 7, v_fvars_2299_);
lean_closure_set(v___f_2321_, 8, v_inst_2289_);
lean_closure_set(v___f_2321_, 9, v_inst_2290_);
lean_closure_set(v___f_2321_, 10, v_inst_2291_);
lean_closure_set(v___f_2321_, 11, v_pre_2292_);
lean_closure_set(v___f_2321_, 12, v_post_2293_);
lean_closure_set(v___f_2321_, 13, v___x_2318_);
lean_closure_set(v___f_2321_, 14, v___x_2319_);
lean_closure_set(v___f_2321_, 15, v___x_2320_);
lean_closure_set(v___f_2321_, 16, v_x_2297_);
lean_closure_set(v___f_2321_, 17, v_x_2298_);
lean_closure_set(v___f_2321_, 18, v_toBind_2312_);
v___x_2322_ = lean_expr_instantiate_rev(v_type_2308_, v_fvars_2299_);
lean_dec_ref(v_fvars_2299_);
lean_dec_ref(v_type_2308_);
v___x_2323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2289_, v_inst_2290_, v_inst_2291_, v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v_x_2297_, v_x_2298_, v___x_2322_, v_a_2301_);
v___x_2324_ = lean_apply_4(v_toBind_2312_, lean_box(0), lean_box(0), v___x_2323_, v___f_2321_);
return v___x_2324_;
}
else
{
lean_object* v_toBind_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___f_2329_; lean_object* v___x_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v___x_2306_);
lean_dec_ref(v___x_2302_);
v_toBind_2325_ = lean_ctor_get(v_inst_2289_, 1);
lean_inc(v_toBind_2325_);
v___x_2326_ = lean_box(v_usedLetOnly_2294_);
v___x_2327_ = lean_box(v_skipConstInApp_2295_);
v___x_2328_ = lean_box(v_skipInstances_2296_);
lean_inc(v_a_2301_);
lean_inc(v_x_2298_);
lean_inc(v_post_2293_);
lean_inc(v_pre_2292_);
lean_inc_ref(v_inst_2291_);
lean_inc(v_inst_2290_);
lean_inc_ref(v_inst_2289_);
v___f_2329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2329_, 0, v_inst_2289_);
lean_closure_set(v___f_2329_, 1, v_inst_2290_);
lean_closure_set(v___f_2329_, 2, v_inst_2291_);
lean_closure_set(v___f_2329_, 3, v_pre_2292_);
lean_closure_set(v___f_2329_, 4, v_post_2293_);
lean_closure_set(v___f_2329_, 5, v___x_2326_);
lean_closure_set(v___f_2329_, 6, v___x_2327_);
lean_closure_set(v___f_2329_, 7, v___x_2328_);
lean_closure_set(v___f_2329_, 8, v_x_2297_);
lean_closure_set(v___f_2329_, 9, v_x_2298_);
lean_closure_set(v___f_2329_, 10, v_a_2301_);
v___x_2330_ = lean_box(v_usedLetOnly_2294_);
lean_inc(v_toBind_2325_);
lean_inc(v_inst_2290_);
lean_inc_ref(v_fvars_2299_);
v___f_2331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2331_, 0, v_fvars_2299_);
lean_closure_set(v___f_2331_, 1, v___x_2330_);
lean_closure_set(v___f_2331_, 2, v_inst_2290_);
lean_closure_set(v___f_2331_, 3, v_toBind_2325_);
lean_closure_set(v___f_2331_, 4, v___f_2329_);
v___x_2332_ = lean_expr_instantiate_rev(v_e_2300_, v_fvars_2299_);
lean_dec_ref(v_fvars_2299_);
lean_dec_ref(v_e_2300_);
v___x_2333_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2289_, v_inst_2290_, v_inst_2291_, v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v_x_2297_, v_x_2298_, v___x_2332_, v_a_2301_);
v___x_2334_ = lean_apply_4(v_toBind_2325_, lean_box(0), lean_box(0), v___x_2333_, v___f_2331_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2335_, lean_object* v_data_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_pre_2340_, lean_object* v_post_2341_, uint8_t v_usedLetOnly_2342_, uint8_t v_skipConstInApp_2343_, uint8_t v_skipInstances_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v_a_2349_){
_start:
{
size_t v___x_2350_; size_t v___x_2351_; uint8_t v___x_2352_; 
v___x_2350_ = lean_ptr_addr(v_expr_2335_);
v___x_2351_ = lean_ptr_addr(v_a_2349_);
v___x_2352_ = lean_usize_dec_eq(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec_ref(v___y_2348_);
v___x_2353_ = l_Lean_Expr_mdata___override(v_data_2336_, v_a_2349_);
v___x_2354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_pre_2340_, v_post_2341_, v_usedLetOnly_2342_, v_skipConstInApp_2343_, v_skipInstances_2344_, v_x_2345_, v_x_2346_, v___x_2353_, v___y_2347_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; 
lean_dec_ref(v_a_2349_);
lean_dec(v_data_2336_);
v___x_2355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_pre_2340_, v_post_2341_, v_usedLetOnly_2342_, v_skipConstInApp_2343_, v_skipInstances_2344_, v_x_2345_, v_x_2346_, v___y_2348_, v___y_2347_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2356_, lean_object* v_data_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_pre_2361_, lean_object* v_post_2362_, lean_object* v_usedLetOnly_2363_, lean_object* v_skipConstInApp_2364_, lean_object* v_skipInstances_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v_a_2370_){
_start:
{
uint8_t v_usedLetOnly_boxed_2371_; uint8_t v_skipConstInApp_boxed_2372_; uint8_t v_skipInstances_boxed_2373_; lean_object* v_res_2374_; 
v_usedLetOnly_boxed_2371_ = lean_unbox(v_usedLetOnly_2363_);
v_skipConstInApp_boxed_2372_ = lean_unbox(v_skipConstInApp_2364_);
v_skipInstances_boxed_2373_ = lean_unbox(v_skipInstances_2365_);
v_res_2374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2356_, v_data_2357_, v_inst_2358_, v_inst_2359_, v_inst_2360_, v_pre_2361_, v_post_2362_, v_usedLetOnly_boxed_2371_, v_skipConstInApp_boxed_2372_, v_skipInstances_boxed_2373_, v_x_2366_, v_x_2367_, v___y_2368_, v___y_2369_, v_a_2370_);
lean_dec_ref(v_expr_2356_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2375_, lean_object* v_typeName_2376_, lean_object* v_idx_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_pre_2381_, lean_object* v_post_2382_, uint8_t v_usedLetOnly_2383_, uint8_t v_skipConstInApp_2384_, uint8_t v_skipInstances_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v_a_2390_){
_start:
{
size_t v___x_2391_; size_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2391_ = lean_ptr_addr(v_struct_2375_);
v___x_2392_ = lean_ptr_addr(v_a_2390_);
v___x_2393_ = lean_usize_dec_eq(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v___y_2389_);
v___x_2394_ = l_Lean_Expr_proj___override(v_typeName_2376_, v_idx_2377_, v_a_2390_);
v___x_2395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2378_, v_inst_2379_, v_inst_2380_, v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v_x_2386_, v_x_2387_, v___x_2394_, v___y_2388_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v_a_2390_);
lean_dec(v_idx_2377_);
lean_dec(v_typeName_2376_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2378_, v_inst_2379_, v_inst_2380_, v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v_x_2386_, v_x_2387_, v___y_2389_, v___y_2388_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2397_, lean_object* v_typeName_2398_, lean_object* v_idx_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_pre_2403_, lean_object* v_post_2404_, lean_object* v_usedLetOnly_2405_, lean_object* v_skipConstInApp_2406_, lean_object* v_skipInstances_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v_a_2412_){
_start:
{
uint8_t v_usedLetOnly_boxed_2413_; uint8_t v_skipConstInApp_boxed_2414_; uint8_t v_skipInstances_boxed_2415_; lean_object* v_res_2416_; 
v_usedLetOnly_boxed_2413_ = lean_unbox(v_usedLetOnly_2405_);
v_skipConstInApp_boxed_2414_ = lean_unbox(v_skipConstInApp_2406_);
v_skipInstances_boxed_2415_ = lean_unbox(v_skipInstances_2407_);
v_res_2416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2397_, v_typeName_2398_, v_idx_2399_, v_inst_2400_, v_inst_2401_, v_inst_2402_, v_pre_2403_, v_post_2404_, v_usedLetOnly_boxed_2413_, v_skipConstInApp_boxed_2414_, v_skipInstances_boxed_2415_, v_x_2408_, v_x_2409_, v___y_2410_, v___y_2411_, v_a_2412_);
lean_dec_ref(v_struct_2397_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_pre_2421_, lean_object* v_post_2422_, uint8_t v_usedLetOnly_2423_, uint8_t v_skipConstInApp_2424_, uint8_t v_skipInstances_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_, lean_object* v___f_2428_, lean_object* v_toBind_2429_, lean_object* v_e_2430_, lean_object* v_____do__lift_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___y_2434_; 
switch(lean_obj_tag(v_____do__lift_2431_))
{
case 0:
{
lean_object* v_e_2466_; lean_object* v_toPure_2467_; lean_object* v___x_2468_; 
lean_dec(v___y_2432_);
lean_dec_ref(v_e_2430_);
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
lean_dec(v_x_2427_);
lean_dec(v_post_2422_);
lean_dec(v_pre_2421_);
lean_dec_ref(v_inst_2420_);
lean_dec(v_inst_2419_);
lean_dec_ref(v_inst_2418_);
v_e_2466_ = lean_ctor_get(v_____do__lift_2431_, 0);
lean_inc_ref(v_e_2466_);
lean_dec_ref(v_____do__lift_2431_);
v_toPure_2467_ = lean_ctor_get(v_toApplicative_2417_, 1);
lean_inc(v_toPure_2467_);
lean_dec_ref(v_toApplicative_2417_);
v___x_2468_ = lean_apply_2(v_toPure_2467_, lean_box(0), v_e_2466_);
return v___x_2468_;
}
case 1:
{
lean_object* v_e_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v_e_2430_);
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
lean_dec_ref(v_toApplicative_2417_);
v_e_2469_ = lean_ctor_get(v_____do__lift_2431_, 0);
lean_inc_ref(v_e_2469_);
lean_dec_ref(v_____do__lift_2431_);
v___x_2470_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v_e_2469_, v___y_2432_);
return v___x_2470_;
}
default: 
{
lean_object* v_e_x3f_2471_; 
lean_dec_ref(v_toApplicative_2417_);
v_e_x3f_2471_ = lean_ctor_get(v_____do__lift_2431_, 0);
lean_inc(v_e_x3f_2471_);
lean_dec_ref(v_____do__lift_2431_);
if (lean_obj_tag(v_e_x3f_2471_) == 0)
{
v___y_2434_ = v_e_2430_;
goto v___jp_2433_;
}
else
{
lean_object* v_val_2472_; 
lean_dec_ref(v_e_2430_);
v_val_2472_ = lean_ctor_get(v_e_x3f_2471_, 0);
lean_inc(v_val_2472_);
lean_dec_ref(v_e_x3f_2471_);
v___y_2434_ = v_val_2472_;
goto v___jp_2433_;
}
}
}
v___jp_2433_:
{
switch(lean_obj_tag(v___y_2434_))
{
case 7:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2436_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v___x_2435_, v___y_2434_, v___y_2432_);
return v___x_2436_;
}
case 6:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v___x_2437_, v___y_2434_, v___y_2432_);
return v___x_2438_;
}
case 8:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v___x_2439_, v___y_2434_, v___y_2432_);
return v___x_2440_;
}
case 5:
{
lean_object* v_dummy_2441_; lean_object* v_nargs_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_3997__overap_2446_; lean_object* v___x_2447_; 
lean_dec(v_toBind_2429_);
lean_dec(v_x_2427_);
lean_dec(v_post_2422_);
lean_dec(v_pre_2421_);
lean_dec_ref(v_inst_2420_);
lean_dec(v_inst_2419_);
lean_dec_ref(v_inst_2418_);
v_dummy_2441_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2442_ = l_Lean_Expr_getAppNumArgs(v___y_2434_);
lean_inc(v_nargs_2442_);
v___x_2443_ = lean_mk_array(v_nargs_2442_, v_dummy_2441_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_sub(v_nargs_2442_, v___x_2444_);
lean_dec(v_nargs_2442_);
v___x_3997__overap_2446_ = l_Lean_Expr_withAppAux___redArg(v___f_2428_, v___y_2434_, v___x_2443_, v___x_2445_);
v___x_2447_ = lean_apply_1(v___x_3997__overap_2446_, v___y_2432_);
return v___x_2447_;
}
case 10:
{
lean_object* v_data_2448_; lean_object* v_expr_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec(v___f_2428_);
v_data_2448_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_data_2448_);
v_expr_2449_ = lean_ctor_get(v___y_2434_, 1);
lean_inc_ref(v_expr_2449_);
v___x_2450_ = lean_box(v_usedLetOnly_2423_);
v___x_2451_ = lean_box(v_skipConstInApp_2424_);
v___x_2452_ = lean_box(v_skipInstances_2425_);
lean_inc(v___y_2432_);
lean_inc(v_x_2427_);
lean_inc(v_post_2422_);
lean_inc(v_pre_2421_);
lean_inc_ref(v_inst_2420_);
lean_inc(v_inst_2419_);
lean_inc_ref(v_inst_2418_);
lean_inc_ref(v_expr_2449_);
v___f_2453_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2453_, 0, v_expr_2449_);
lean_closure_set(v___f_2453_, 1, v_data_2448_);
lean_closure_set(v___f_2453_, 2, v_inst_2418_);
lean_closure_set(v___f_2453_, 3, v_inst_2419_);
lean_closure_set(v___f_2453_, 4, v_inst_2420_);
lean_closure_set(v___f_2453_, 5, v_pre_2421_);
lean_closure_set(v___f_2453_, 6, v_post_2422_);
lean_closure_set(v___f_2453_, 7, v___x_2450_);
lean_closure_set(v___f_2453_, 8, v___x_2451_);
lean_closure_set(v___f_2453_, 9, v___x_2452_);
lean_closure_set(v___f_2453_, 10, v_x_2426_);
lean_closure_set(v___f_2453_, 11, v_x_2427_);
lean_closure_set(v___f_2453_, 12, v___y_2432_);
lean_closure_set(v___f_2453_, 13, v___y_2434_);
v___x_2454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v_expr_2449_, v___y_2432_);
v___x_2455_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2454_, v___f_2453_);
return v___x_2455_;
}
case 11:
{
lean_object* v_typeName_2456_; lean_object* v_idx_2457_; lean_object* v_struct_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec(v___f_2428_);
v_typeName_2456_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_typeName_2456_);
v_idx_2457_ = lean_ctor_get(v___y_2434_, 1);
lean_inc(v_idx_2457_);
v_struct_2458_ = lean_ctor_get(v___y_2434_, 2);
lean_inc_ref(v_struct_2458_);
v___x_2459_ = lean_box(v_usedLetOnly_2423_);
v___x_2460_ = lean_box(v_skipConstInApp_2424_);
v___x_2461_ = lean_box(v_skipInstances_2425_);
lean_inc(v___y_2432_);
lean_inc(v_x_2427_);
lean_inc(v_post_2422_);
lean_inc(v_pre_2421_);
lean_inc_ref(v_inst_2420_);
lean_inc(v_inst_2419_);
lean_inc_ref(v_inst_2418_);
lean_inc_ref(v_struct_2458_);
v___f_2462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2462_, 0, v_struct_2458_);
lean_closure_set(v___f_2462_, 1, v_typeName_2456_);
lean_closure_set(v___f_2462_, 2, v_idx_2457_);
lean_closure_set(v___f_2462_, 3, v_inst_2418_);
lean_closure_set(v___f_2462_, 4, v_inst_2419_);
lean_closure_set(v___f_2462_, 5, v_inst_2420_);
lean_closure_set(v___f_2462_, 6, v_pre_2421_);
lean_closure_set(v___f_2462_, 7, v_post_2422_);
lean_closure_set(v___f_2462_, 8, v___x_2459_);
lean_closure_set(v___f_2462_, 9, v___x_2460_);
lean_closure_set(v___f_2462_, 10, v___x_2461_);
lean_closure_set(v___f_2462_, 11, v_x_2426_);
lean_closure_set(v___f_2462_, 12, v_x_2427_);
lean_closure_set(v___f_2462_, 13, v___y_2432_);
lean_closure_set(v___f_2462_, 14, v___y_2434_);
v___x_2463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v_struct_2458_, v___y_2432_);
v___x_2464_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2463_, v___f_2462_);
return v___x_2464_;
}
default: 
{
lean_object* v___x_2465_; 
lean_dec(v_toBind_2429_);
lean_dec(v___f_2428_);
v___x_2465_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v___y_2434_, v___y_2432_);
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_pre_2477_, lean_object* v_post_2478_, lean_object* v_usedLetOnly_2479_, lean_object* v_skipConstInApp_2480_, lean_object* v_skipInstances_2481_, lean_object* v_x_2482_, lean_object* v_x_2483_, lean_object* v___f_2484_, lean_object* v_toBind_2485_, lean_object* v_e_2486_, lean_object* v_____do__lift_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v_usedLetOnly_boxed_2489_; uint8_t v_skipConstInApp_boxed_2490_; uint8_t v_skipInstances_boxed_2491_; lean_object* v_res_2492_; 
v_usedLetOnly_boxed_2489_ = lean_unbox(v_usedLetOnly_2479_);
v_skipConstInApp_boxed_2490_ = lean_unbox(v_skipConstInApp_2480_);
v_skipInstances_boxed_2491_ = lean_unbox(v_skipInstances_2481_);
v_res_2492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2473_, v_inst_2474_, v_inst_2475_, v_inst_2476_, v_pre_2477_, v_post_2478_, v_usedLetOnly_boxed_2489_, v_skipConstInApp_boxed_2490_, v_skipInstances_boxed_2491_, v_x_2482_, v_x_2483_, v___f_2484_, v_toBind_2485_, v_e_2486_, v_____do__lift_2487_, v___y_2488_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_pre_2496_, lean_object* v_post_2497_, uint8_t v_usedLetOnly_2498_, uint8_t v_skipConstInApp_2499_, uint8_t v_skipInstances_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_, lean_object* v_e_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v_toApplicative_2510_; lean_object* v_toBind_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___f_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_inc_ref(v_inst_2493_);
v___x_2505_ = l_ReaderT_instMonad___redArg(v_inst_2493_);
v___x_2506_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0);
lean_inc_ref(v_inst_2495_);
v___f_2507_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2507_, 0, v___x_2506_);
lean_closure_set(v___f_2507_, 1, v_inst_2495_);
lean_inc_ref(v_inst_2495_);
v___f_2508_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2508_, 0, v___x_2506_);
lean_closure_set(v___f_2508_, 1, v_inst_2495_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___f_2507_);
lean_ctor_set(v___x_2509_, 1, v___f_2508_);
v_toApplicative_2510_ = lean_ctor_get(v_inst_2493_, 0);
lean_inc_ref(v_toApplicative_2510_);
v_toBind_2511_ = lean_ctor_get(v_inst_2493_, 1);
lean_inc(v_toBind_2511_);
lean_inc_ref(v_toApplicative_2510_);
v___f_2512_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2512_, 0, v_toApplicative_2510_);
v___x_2513_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
v___x_2514_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__2));
lean_inc(v_toBind_2511_);
lean_inc(v_x_2502_);
lean_inc(v_a_2504_);
lean_inc_ref(v_e_2503_);
lean_inc_ref(v_toApplicative_2510_);
v___f_2515_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2515_, 0, v_toApplicative_2510_);
lean_closure_set(v___f_2515_, 1, v___x_2513_);
lean_closure_set(v___f_2515_, 2, v___x_2514_);
lean_closure_set(v___f_2515_, 3, v_e_2503_);
lean_closure_set(v___f_2515_, 4, v_a_2504_);
lean_closure_set(v___f_2515_, 5, v_x_2502_);
lean_closure_set(v___f_2515_, 6, v_toBind_2511_);
lean_inc_ref(v_e_2503_);
lean_inc_ref(v_toApplicative_2510_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2516_, 0, v_toApplicative_2510_);
lean_closure_set(v___f_2516_, 1, v___x_2513_);
lean_closure_set(v___f_2516_, 2, v___x_2514_);
lean_closure_set(v___f_2516_, 3, v_e_2503_);
v___x_2517_ = lean_box(v_skipInstances_2500_);
v___x_2518_ = lean_box(v_usedLetOnly_2498_);
v___x_2519_ = lean_box(v_skipConstInApp_2499_);
lean_inc_ref(v_toApplicative_2510_);
lean_inc(v_toBind_2511_);
lean_inc_ref(v___x_2505_);
lean_inc(v_x_2502_);
lean_inc(v_post_2497_);
lean_inc(v_pre_2496_);
lean_inc_ref(v_inst_2495_);
lean_inc(v_inst_2494_);
lean_inc_ref(v_inst_2493_);
v___f_2520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2520_, 0, v___x_2517_);
lean_closure_set(v___f_2520_, 1, v_inst_2493_);
lean_closure_set(v___f_2520_, 2, v_inst_2494_);
lean_closure_set(v___f_2520_, 3, v_inst_2495_);
lean_closure_set(v___f_2520_, 4, v_pre_2496_);
lean_closure_set(v___f_2520_, 5, v_post_2497_);
lean_closure_set(v___f_2520_, 6, v___x_2518_);
lean_closure_set(v___f_2520_, 7, v___x_2519_);
lean_closure_set(v___f_2520_, 8, v_x_2501_);
lean_closure_set(v___f_2520_, 9, v_x_2502_);
lean_closure_set(v___f_2520_, 10, v___x_2505_);
lean_closure_set(v___f_2520_, 11, v_toBind_2511_);
lean_closure_set(v___f_2520_, 12, v_toApplicative_2510_);
lean_closure_set(v___f_2520_, 13, v___f_2512_);
v___x_2521_ = lean_box(v_usedLetOnly_2498_);
v___x_2522_ = lean_box(v_skipConstInApp_2499_);
v___x_2523_ = lean_box(v_skipInstances_2500_);
lean_inc_ref(v_e_2503_);
lean_inc(v_toBind_2511_);
lean_inc(v_x_2502_);
lean_inc(v_pre_2496_);
lean_inc_ref(v_inst_2493_);
lean_inc_ref(v_toApplicative_2510_);
v___f_2524_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 14);
lean_closure_set(v___f_2524_, 0, v_toApplicative_2510_);
lean_closure_set(v___f_2524_, 1, v_inst_2493_);
lean_closure_set(v___f_2524_, 2, v_inst_2494_);
lean_closure_set(v___f_2524_, 3, v_inst_2495_);
lean_closure_set(v___f_2524_, 4, v_pre_2496_);
lean_closure_set(v___f_2524_, 5, v_post_2497_);
lean_closure_set(v___f_2524_, 6, v___x_2521_);
lean_closure_set(v___f_2524_, 7, v___x_2522_);
lean_closure_set(v___f_2524_, 8, v___x_2523_);
lean_closure_set(v___f_2524_, 9, v_x_2501_);
lean_closure_set(v___f_2524_, 10, v_x_2502_);
lean_closure_set(v___f_2524_, 11, v___f_2520_);
lean_closure_set(v___f_2524_, 12, v_toBind_2511_);
lean_closure_set(v___f_2524_, 13, v_e_2503_);
lean_inc(v_toBind_2511_);
lean_inc(v_a_2504_);
v___f_2525_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12), 11, 10);
lean_closure_set(v___f_2525_, 0, v_pre_2496_);
lean_closure_set(v___f_2525_, 1, v_e_2503_);
lean_closure_set(v___f_2525_, 2, v_inst_2493_);
lean_closure_set(v___f_2525_, 3, v___f_2524_);
lean_closure_set(v___f_2525_, 4, v___x_2509_);
lean_closure_set(v___f_2525_, 5, v___x_2505_);
lean_closure_set(v___f_2525_, 6, v_a_2504_);
lean_closure_set(v___f_2525_, 7, v_toBind_2511_);
lean_closure_set(v___f_2525_, 8, v___f_2515_);
lean_closure_set(v___f_2525_, 9, v_toApplicative_2510_);
v___x_2526_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2526_, 0, lean_box(0));
lean_closure_set(v___x_2526_, 1, lean_box(0));
lean_closure_set(v___x_2526_, 2, v_a_2504_);
v___x_2527_ = lean_apply_2(v_x_2502_, lean_box(0), v___x_2526_);
lean_inc(v_toBind_2511_);
v___x_2528_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v___x_2527_, v___f_2516_);
v___x_2529_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v___x_2528_, v___f_2525_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_pre_2534_, lean_object* v_post_2535_, uint8_t v_usedLetOnly_2536_, uint8_t v_skipConstInApp_2537_, uint8_t v_skipInstances_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, lean_object* v_a_2541_, lean_object* v_e_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___y_2545_; 
switch(lean_obj_tag(v_a_2543_))
{
case 0:
{
lean_object* v_e_2548_; lean_object* v_toPure_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_e_2542_);
lean_dec(v_a_2541_);
lean_dec(v_x_2540_);
lean_dec(v_post_2535_);
lean_dec(v_pre_2534_);
lean_dec_ref(v_inst_2533_);
lean_dec(v_inst_2532_);
lean_dec_ref(v_inst_2531_);
v_e_2548_ = lean_ctor_get(v_a_2543_, 0);
lean_inc_ref(v_e_2548_);
lean_dec_ref(v_a_2543_);
v_toPure_2549_ = lean_ctor_get(v_toApplicative_2530_, 1);
lean_inc(v_toPure_2549_);
lean_dec_ref(v_toApplicative_2530_);
v___x_2550_ = lean_apply_2(v_toPure_2549_, lean_box(0), v_e_2548_);
return v___x_2550_;
}
case 1:
{
lean_object* v_e_2551_; lean_object* v___x_2552_; 
lean_dec_ref(v_e_2542_);
lean_dec_ref(v_toApplicative_2530_);
v_e_2551_ = lean_ctor_get(v_a_2543_, 0);
lean_inc_ref(v_e_2551_);
lean_dec_ref(v_a_2543_);
v___x_2552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2531_, v_inst_2532_, v_inst_2533_, v_pre_2534_, v_post_2535_, v_usedLetOnly_2536_, v_skipConstInApp_2537_, v_skipInstances_2538_, v_x_2539_, v_x_2540_, v_e_2551_, v_a_2541_);
return v___x_2552_;
}
default: 
{
lean_object* v_e_x3f_2553_; 
lean_dec(v_a_2541_);
lean_dec(v_x_2540_);
lean_dec(v_post_2535_);
lean_dec(v_pre_2534_);
lean_dec_ref(v_inst_2533_);
lean_dec(v_inst_2532_);
lean_dec_ref(v_inst_2531_);
v_e_x3f_2553_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_e_x3f_2553_);
lean_dec_ref(v_a_2543_);
if (lean_obj_tag(v_e_x3f_2553_) == 0)
{
v___y_2545_ = v_e_2542_;
goto v___jp_2544_;
}
else
{
lean_object* v_val_2554_; 
lean_dec_ref(v_e_2542_);
v_val_2554_ = lean_ctor_get(v_e_x3f_2553_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v_e_x3f_2553_);
v___y_2545_ = v_val_2554_;
goto v___jp_2544_;
}
}
}
v___jp_2544_:
{
lean_object* v_toPure_2546_; lean_object* v___x_2547_; 
v_toPure_2546_ = lean_ctor_get(v_toApplicative_2530_, 1);
lean_inc(v_toPure_2546_);
lean_dec_ref(v_toApplicative_2530_);
v___x_2547_ = lean_apply_2(v_toPure_2546_, lean_box(0), v___y_2545_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_pre_2559_, lean_object* v_post_2560_, lean_object* v_usedLetOnly_2561_, lean_object* v_skipConstInApp_2562_, lean_object* v_skipInstances_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_a_2566_, lean_object* v_e_2567_, lean_object* v_a_2568_){
_start:
{
uint8_t v_usedLetOnly_boxed_2569_; uint8_t v_skipConstInApp_boxed_2570_; uint8_t v_skipInstances_boxed_2571_; lean_object* v_res_2572_; 
v_usedLetOnly_boxed_2569_ = lean_unbox(v_usedLetOnly_2561_);
v_skipConstInApp_boxed_2570_ = lean_unbox(v_skipConstInApp_2562_);
v_skipInstances_boxed_2571_ = lean_unbox(v_skipInstances_2563_);
v_res_2572_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2555_, v_inst_2556_, v_inst_2557_, v_inst_2558_, v_pre_2559_, v_post_2560_, v_usedLetOnly_boxed_2569_, v_skipConstInApp_boxed_2570_, v_skipInstances_boxed_2571_, v_x_2564_, v_x_2565_, v_a_2566_, v_e_2567_, v_a_2568_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_pre_2576_, lean_object* v_post_2577_, uint8_t v_usedLetOnly_2578_, uint8_t v_skipConstInApp_2579_, uint8_t v_skipInstances_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_e_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_toApplicative_2585_; lean_object* v_toBind_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_toApplicative_2585_ = lean_ctor_get(v_inst_2573_, 0);
lean_inc_ref(v_toApplicative_2585_);
v_toBind_2586_ = lean_ctor_get(v_inst_2573_, 1);
lean_inc(v_toBind_2586_);
v___x_2587_ = lean_box(v_usedLetOnly_2578_);
v___x_2588_ = lean_box(v_skipConstInApp_2579_);
v___x_2589_ = lean_box(v_skipInstances_2580_);
lean_inc_ref(v_e_2583_);
lean_inc(v_post_2577_);
v___f_2590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2590_, 0, v_toApplicative_2585_);
lean_closure_set(v___f_2590_, 1, v_inst_2573_);
lean_closure_set(v___f_2590_, 2, v_inst_2574_);
lean_closure_set(v___f_2590_, 3, v_inst_2575_);
lean_closure_set(v___f_2590_, 4, v_pre_2576_);
lean_closure_set(v___f_2590_, 5, v_post_2577_);
lean_closure_set(v___f_2590_, 6, v___x_2587_);
lean_closure_set(v___f_2590_, 7, v___x_2588_);
lean_closure_set(v___f_2590_, 8, v___x_2589_);
lean_closure_set(v___f_2590_, 9, v_x_2581_);
lean_closure_set(v___f_2590_, 10, v_x_2582_);
lean_closure_set(v___f_2590_, 11, v_a_2584_);
lean_closure_set(v___f_2590_, 12, v_e_2583_);
v___x_2591_ = lean_apply_1(v_post_2577_, v_e_2583_);
v___x_2592_ = lean_apply_4(v_toBind_2586_, lean_box(0), lean_box(0), v___x_2591_, v___f_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_pre_2596_, lean_object* v_post_2597_, uint8_t v_usedLetOnly_2598_, uint8_t v_skipConstInApp_2599_, uint8_t v_skipInstances_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2593_, v_inst_2594_, v_inst_2595_, v_pre_2596_, v_post_2597_, v_usedLetOnly_2598_, v_skipConstInApp_2599_, v_skipInstances_2600_, v_x_2601_, v_x_2602_, v_a_2604_, v_a_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_pre_2609_, lean_object* v_post_2610_, lean_object* v_usedLetOnly_2611_, lean_object* v_skipConstInApp_2612_, lean_object* v_skipInstances_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_, lean_object* v_e_2616_, lean_object* v_a_2617_){
_start:
{
uint8_t v_usedLetOnly_boxed_2618_; uint8_t v_skipConstInApp_boxed_2619_; uint8_t v_skipInstances_boxed_2620_; lean_object* v_res_2621_; 
v_usedLetOnly_boxed_2618_ = lean_unbox(v_usedLetOnly_2611_);
v_skipConstInApp_boxed_2619_ = lean_unbox(v_skipConstInApp_2612_);
v_skipInstances_boxed_2620_ = lean_unbox(v_skipInstances_2613_);
v_res_2621_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2606_, v_inst_2607_, v_inst_2608_, v_pre_2609_, v_post_2610_, v_usedLetOnly_boxed_2618_, v_skipConstInApp_boxed_2619_, v_skipInstances_boxed_2620_, v_x_2614_, v_x_2615_, v_e_2616_, v_a_2617_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_pre_2625_, lean_object* v_post_2626_, lean_object* v_usedLetOnly_2627_, lean_object* v_skipConstInApp_2628_, lean_object* v_skipInstances_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_fvars_2632_, lean_object* v_e_2633_, lean_object* v_a_2634_){
_start:
{
uint8_t v_usedLetOnly_boxed_2635_; uint8_t v_skipConstInApp_boxed_2636_; uint8_t v_skipInstances_boxed_2637_; lean_object* v_res_2638_; 
v_usedLetOnly_boxed_2635_ = lean_unbox(v_usedLetOnly_2627_);
v_skipConstInApp_boxed_2636_ = lean_unbox(v_skipConstInApp_2628_);
v_skipInstances_boxed_2637_ = lean_unbox(v_skipInstances_2629_);
v_res_2638_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2622_, v_inst_2623_, v_inst_2624_, v_pre_2625_, v_post_2626_, v_usedLetOnly_boxed_2635_, v_skipConstInApp_boxed_2636_, v_skipInstances_boxed_2637_, v_x_2630_, v_x_2631_, v_fvars_2632_, v_e_2633_, v_a_2634_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_pre_2642_, lean_object* v_post_2643_, lean_object* v_usedLetOnly_2644_, lean_object* v_skipConstInApp_2645_, lean_object* v_skipInstances_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_, lean_object* v_fvars_2649_, lean_object* v_e_2650_, lean_object* v_a_2651_){
_start:
{
uint8_t v_usedLetOnly_boxed_2652_; uint8_t v_skipConstInApp_boxed_2653_; uint8_t v_skipInstances_boxed_2654_; lean_object* v_res_2655_; 
v_usedLetOnly_boxed_2652_ = lean_unbox(v_usedLetOnly_2644_);
v_skipConstInApp_boxed_2653_ = lean_unbox(v_skipConstInApp_2645_);
v_skipInstances_boxed_2654_ = lean_unbox(v_skipInstances_2646_);
v_res_2655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2639_, v_inst_2640_, v_inst_2641_, v_pre_2642_, v_post_2643_, v_usedLetOnly_boxed_2652_, v_skipConstInApp_boxed_2653_, v_skipInstances_boxed_2654_, v_x_2647_, v_x_2648_, v_fvars_2649_, v_e_2650_, v_a_2651_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_pre_2659_, lean_object* v_post_2660_, lean_object* v_usedLetOnly_2661_, lean_object* v_skipConstInApp_2662_, lean_object* v_skipInstances_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_fvars_2666_, lean_object* v_e_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_usedLetOnly_boxed_2669_; uint8_t v_skipConstInApp_boxed_2670_; uint8_t v_skipInstances_boxed_2671_; lean_object* v_res_2672_; 
v_usedLetOnly_boxed_2669_ = lean_unbox(v_usedLetOnly_2661_);
v_skipConstInApp_boxed_2670_ = lean_unbox(v_skipConstInApp_2662_);
v_skipInstances_boxed_2671_ = lean_unbox(v_skipInstances_2663_);
v_res_2672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2656_, v_inst_2657_, v_inst_2658_, v_pre_2659_, v_post_2660_, v_usedLetOnly_boxed_2669_, v_skipConstInApp_boxed_2670_, v_skipInstances_boxed_2671_, v_x_2664_, v_x_2665_, v_fvars_2666_, v_e_2667_, v_a_2668_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_pre_2677_, lean_object* v_post_2678_, uint8_t v_usedLetOnly_2679_, uint8_t v_skipConstInApp_2680_, uint8_t v_skipInstances_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v_e_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v_e_2684_, v_a_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_pre_2691_, lean_object* v_post_2692_, lean_object* v_usedLetOnly_2693_, lean_object* v_skipConstInApp_2694_, lean_object* v_skipInstances_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_, lean_object* v_e_2698_, lean_object* v_a_2699_){
_start:
{
uint8_t v_usedLetOnly_boxed_2700_; uint8_t v_skipConstInApp_boxed_2701_; uint8_t v_skipInstances_boxed_2702_; lean_object* v_res_2703_; 
v_usedLetOnly_boxed_2700_ = lean_unbox(v_usedLetOnly_2693_);
v_skipConstInApp_boxed_2701_ = lean_unbox(v_skipConstInApp_2694_);
v_skipInstances_boxed_2702_ = lean_unbox(v_skipInstances_2695_);
v_res_2703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2687_, v_inst_2688_, v_inst_2689_, v_inst_2690_, v_pre_2691_, v_post_2692_, v_usedLetOnly_boxed_2700_, v_skipConstInApp_boxed_2701_, v_skipInstances_boxed_2702_, v_x_2696_, v_x_2697_, v_e_2698_, v_a_2699_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_pre_2708_, lean_object* v_post_2709_, uint8_t v_usedLetOnly_2710_, uint8_t v_skipConstInApp_2711_, uint8_t v_skipInstances_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_, lean_object* v_fvars_2715_, lean_object* v_e_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2705_, v_inst_2706_, v_inst_2707_, v_pre_2708_, v_post_2709_, v_usedLetOnly_2710_, v_skipConstInApp_2711_, v_skipInstances_2712_, v_x_2713_, v_x_2714_, v_fvars_2715_, v_e_2716_, v_a_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_pre_2723_, lean_object* v_post_2724_, lean_object* v_usedLetOnly_2725_, lean_object* v_skipConstInApp_2726_, lean_object* v_skipInstances_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_fvars_2730_, lean_object* v_e_2731_, lean_object* v_a_2732_){
_start:
{
uint8_t v_usedLetOnly_boxed_2733_; uint8_t v_skipConstInApp_boxed_2734_; uint8_t v_skipInstances_boxed_2735_; lean_object* v_res_2736_; 
v_usedLetOnly_boxed_2733_ = lean_unbox(v_usedLetOnly_2725_);
v_skipConstInApp_boxed_2734_ = lean_unbox(v_skipConstInApp_2726_);
v_skipInstances_boxed_2735_ = lean_unbox(v_skipInstances_2727_);
v_res_2736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_boxed_2733_, v_skipConstInApp_boxed_2734_, v_skipInstances_boxed_2735_, v_x_2728_, v_x_2729_, v_fvars_2730_, v_e_2731_, v_a_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_pre_2741_, lean_object* v_post_2742_, uint8_t v_usedLetOnly_2743_, uint8_t v_skipConstInApp_2744_, uint8_t v_skipInstances_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_e_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2738_, v_inst_2739_, v_inst_2740_, v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_x_2746_, v_x_2747_, v_e_2748_, v_a_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_pre_2755_, lean_object* v_post_2756_, lean_object* v_usedLetOnly_2757_, lean_object* v_skipConstInApp_2758_, lean_object* v_skipInstances_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_e_2762_, lean_object* v_a_2763_){
_start:
{
uint8_t v_usedLetOnly_boxed_2764_; uint8_t v_skipConstInApp_boxed_2765_; uint8_t v_skipInstances_boxed_2766_; lean_object* v_res_2767_; 
v_usedLetOnly_boxed_2764_ = lean_unbox(v_usedLetOnly_2757_);
v_skipConstInApp_boxed_2765_ = lean_unbox(v_skipConstInApp_2758_);
v_skipInstances_boxed_2766_ = lean_unbox(v_skipInstances_2759_);
v_res_2767_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_2751_, v_inst_2752_, v_inst_2753_, v_inst_2754_, v_pre_2755_, v_post_2756_, v_usedLetOnly_boxed_2764_, v_skipConstInApp_boxed_2765_, v_skipInstances_boxed_2766_, v_x_2760_, v_x_2761_, v_e_2762_, v_a_2763_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_pre_2772_, lean_object* v_post_2773_, uint8_t v_usedLetOnly_2774_, uint8_t v_skipConstInApp_2775_, uint8_t v_skipInstances_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_fvars_2779_, lean_object* v_e_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2769_, v_inst_2770_, v_inst_2771_, v_pre_2772_, v_post_2773_, v_usedLetOnly_2774_, v_skipConstInApp_2775_, v_skipInstances_2776_, v_x_2777_, v_x_2778_, v_fvars_2779_, v_e_2780_, v_a_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_pre_2787_, lean_object* v_post_2788_, lean_object* v_usedLetOnly_2789_, lean_object* v_skipConstInApp_2790_, lean_object* v_skipInstances_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v_fvars_2794_, lean_object* v_e_2795_, lean_object* v_a_2796_){
_start:
{
uint8_t v_usedLetOnly_boxed_2797_; uint8_t v_skipConstInApp_boxed_2798_; uint8_t v_skipInstances_boxed_2799_; lean_object* v_res_2800_; 
v_usedLetOnly_boxed_2797_ = lean_unbox(v_usedLetOnly_2789_);
v_skipConstInApp_boxed_2798_ = lean_unbox(v_skipConstInApp_2790_);
v_skipInstances_boxed_2799_ = lean_unbox(v_skipInstances_2791_);
v_res_2800_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_2783_, v_inst_2784_, v_inst_2785_, v_inst_2786_, v_pre_2787_, v_post_2788_, v_usedLetOnly_boxed_2797_, v_skipConstInApp_boxed_2798_, v_skipInstances_boxed_2799_, v_x_2792_, v_x_2793_, v_fvars_2794_, v_e_2795_, v_a_2796_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_pre_2805_, lean_object* v_post_2806_, uint8_t v_usedLetOnly_2807_, uint8_t v_skipConstInApp_2808_, uint8_t v_skipInstances_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_fvars_2812_, lean_object* v_e_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2802_, v_inst_2803_, v_inst_2804_, v_pre_2805_, v_post_2806_, v_usedLetOnly_2807_, v_skipConstInApp_2808_, v_skipInstances_2809_, v_x_2810_, v_x_2811_, v_fvars_2812_, v_e_2813_, v_a_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_2816_, lean_object* v_inst_2817_, lean_object* v_inst_2818_, lean_object* v_inst_2819_, lean_object* v_pre_2820_, lean_object* v_post_2821_, lean_object* v_usedLetOnly_2822_, lean_object* v_skipConstInApp_2823_, lean_object* v_skipInstances_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_fvars_2827_, lean_object* v_e_2828_, lean_object* v_a_2829_){
_start:
{
uint8_t v_usedLetOnly_boxed_2830_; uint8_t v_skipConstInApp_boxed_2831_; uint8_t v_skipInstances_boxed_2832_; lean_object* v_res_2833_; 
v_usedLetOnly_boxed_2830_ = lean_unbox(v_usedLetOnly_2822_);
v_skipConstInApp_boxed_2831_ = lean_unbox(v_skipConstInApp_2823_);
v_skipInstances_boxed_2832_ = lean_unbox(v_skipInstances_2824_);
v_res_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_2816_, v_inst_2817_, v_inst_2818_, v_inst_2819_, v_pre_2820_, v_post_2821_, v_usedLetOnly_boxed_2830_, v_skipConstInApp_boxed_2831_, v_skipInstances_boxed_2832_, v_x_2825_, v_x_2826_, v_fvars_2827_, v_e_2828_, v_a_2829_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_apply_1(v_x_2834_, lean_box(0));
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_2849_, lean_object* v_00_u03b1_2850_, lean_object* v_x_2851_){
_start:
{
lean_object* v___f_2852_; lean_object* v___x_2853_; 
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2852_, 0, v_x_2851_);
v___x_2853_ = lean_apply_2(v_inst_2849_, lean_box(0), v___f_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_2854_, lean_object* v_x_2855_, lean_object* v_toBind_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_pre_2860_, lean_object* v_post_2861_, uint8_t v_usedLetOnly_2862_, uint8_t v_skipConstInApp_2863_, uint8_t v_skipInstances_2864_, lean_object* v_x_2865_, lean_object* v_input_2866_, lean_object* v_ref_2867_){
_start:
{
lean_object* v___f_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_inc(v_toBind_2856_);
lean_inc(v_x_2855_);
lean_inc(v_ref_2867_);
v___f_2868_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2868_, 0, v_toPure_2854_);
lean_closure_set(v___f_2868_, 1, v_ref_2867_);
lean_closure_set(v___f_2868_, 2, v_x_2855_);
lean_closure_set(v___f_2868_, 3, v_toBind_2856_);
v___x_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2857_, v_inst_2858_, v_inst_2859_, v_pre_2860_, v_post_2861_, v_usedLetOnly_2862_, v_skipConstInApp_2863_, v_skipInstances_2864_, v_x_2865_, v_x_2855_, v_input_2866_, v_ref_2867_);
v___x_2870_ = lean_apply_4(v_toBind_2856_, lean_box(0), lean_box(0), v___x_2869_, v___f_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_2871_, lean_object* v_x_2872_, lean_object* v_toBind_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_pre_2877_, lean_object* v_post_2878_, lean_object* v_usedLetOnly_2879_, lean_object* v_skipConstInApp_2880_, lean_object* v_skipInstances_2881_, lean_object* v_x_2882_, lean_object* v_input_2883_, lean_object* v_ref_2884_){
_start:
{
uint8_t v_usedLetOnly_boxed_2885_; uint8_t v_skipConstInApp_boxed_2886_; uint8_t v_skipInstances_boxed_2887_; lean_object* v_res_2888_; 
v_usedLetOnly_boxed_2885_ = lean_unbox(v_usedLetOnly_2879_);
v_skipConstInApp_boxed_2886_ = lean_unbox(v_skipConstInApp_2880_);
v_skipInstances_boxed_2887_ = lean_unbox(v_skipInstances_2881_);
v_res_2888_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_2871_, v_x_2872_, v_toBind_2873_, v_inst_2874_, v_inst_2875_, v_inst_2876_, v_pre_2877_, v_post_2878_, v_usedLetOnly_boxed_2885_, v_skipConstInApp_boxed_2886_, v_skipInstances_boxed_2887_, v_x_2882_, v_input_2883_, v_ref_2884_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_input_2892_, lean_object* v_cache_2893_, lean_object* v_pre_2894_, lean_object* v_post_2895_, uint8_t v_usedLetOnly_2896_, uint8_t v_skipConstInApp_2897_, uint8_t v_skipInstances_2898_){
_start:
{
lean_object* v_x_2899_; lean_object* v_toApplicative_2900_; lean_object* v_toBind_2901_; lean_object* v_toPure_2902_; lean_object* v_x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; 
v_x_2899_ = lean_box(0);
v_toApplicative_2900_ = lean_ctor_get(v_inst_2889_, 0);
v_toBind_2901_ = lean_ctor_get(v_inst_2889_, 1);
lean_inc(v_toBind_2901_);
v_toPure_2902_ = lean_ctor_get(v_toApplicative_2900_, 1);
lean_inc(v_toPure_2902_);
lean_inc(v_inst_2890_);
v_x_2903_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_2903_, 0, v_inst_2890_);
v___x_2904_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2904_, 0, lean_box(0));
lean_closure_set(v___x_2904_, 1, lean_box(0));
lean_closure_set(v___x_2904_, 2, v_cache_2893_);
lean_inc(v_inst_2890_);
v___x_2905_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_2890_, lean_box(0), v___x_2904_);
v___x_2906_ = lean_box(v_usedLetOnly_2896_);
v___x_2907_ = lean_box(v_skipConstInApp_2897_);
v___x_2908_ = lean_box(v_skipInstances_2898_);
lean_inc(v_toBind_2901_);
v___f_2909_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_2909_, 0, v_toPure_2902_);
lean_closure_set(v___f_2909_, 1, v_x_2903_);
lean_closure_set(v___f_2909_, 2, v_toBind_2901_);
lean_closure_set(v___f_2909_, 3, v_inst_2889_);
lean_closure_set(v___f_2909_, 4, v_inst_2890_);
lean_closure_set(v___f_2909_, 5, v_inst_2891_);
lean_closure_set(v___f_2909_, 6, v_pre_2894_);
lean_closure_set(v___f_2909_, 7, v_post_2895_);
lean_closure_set(v___f_2909_, 8, v___x_2906_);
lean_closure_set(v___f_2909_, 9, v___x_2907_);
lean_closure_set(v___f_2909_, 10, v___x_2908_);
lean_closure_set(v___f_2909_, 11, v_x_2899_);
lean_closure_set(v___f_2909_, 12, v_input_2892_);
v___x_2910_ = lean_apply_4(v_toBind_2901_, lean_box(0), lean_box(0), v___x_2905_, v___f_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_input_2914_, lean_object* v_cache_2915_, lean_object* v_pre_2916_, lean_object* v_post_2917_, lean_object* v_usedLetOnly_2918_, lean_object* v_skipConstInApp_2919_, lean_object* v_skipInstances_2920_){
_start:
{
uint8_t v_usedLetOnly_boxed_2921_; uint8_t v_skipConstInApp_boxed_2922_; uint8_t v_skipInstances_boxed_2923_; lean_object* v_res_2924_; 
v_usedLetOnly_boxed_2921_ = lean_unbox(v_usedLetOnly_2918_);
v_skipConstInApp_boxed_2922_ = lean_unbox(v_skipConstInApp_2919_);
v_skipInstances_boxed_2923_ = lean_unbox(v_skipInstances_2920_);
v_res_2924_ = l_Lean_Meta_transformWithCache___redArg(v_inst_2911_, v_inst_2912_, v_inst_2913_, v_input_2914_, v_cache_2915_, v_pre_2916_, v_post_2917_, v_usedLetOnly_boxed_2921_, v_skipConstInApp_boxed_2922_, v_skipInstances_boxed_2923_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_input_2929_, lean_object* v_cache_2930_, lean_object* v_pre_2931_, lean_object* v_post_2932_, uint8_t v_usedLetOnly_2933_, uint8_t v_skipConstInApp_2934_, uint8_t v_skipInstances_2935_){
_start:
{
lean_object* v_x_2936_; lean_object* v_toApplicative_2937_; lean_object* v_toBind_2938_; lean_object* v_toPure_2939_; lean_object* v_x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; 
v_x_2936_ = lean_box(0);
v_toApplicative_2937_ = lean_ctor_get(v_inst_2926_, 0);
v_toBind_2938_ = lean_ctor_get(v_inst_2926_, 1);
lean_inc(v_toBind_2938_);
v_toPure_2939_ = lean_ctor_get(v_toApplicative_2937_, 1);
lean_inc(v_toPure_2939_);
lean_inc(v_inst_2927_);
v_x_2940_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_2940_, 0, v_inst_2927_);
v___x_2941_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2941_, 0, lean_box(0));
lean_closure_set(v___x_2941_, 1, lean_box(0));
lean_closure_set(v___x_2941_, 2, v_cache_2930_);
lean_inc(v_inst_2927_);
v___x_2942_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_2927_, lean_box(0), v___x_2941_);
v___x_2943_ = lean_box(v_usedLetOnly_2933_);
v___x_2944_ = lean_box(v_skipConstInApp_2934_);
v___x_2945_ = lean_box(v_skipInstances_2935_);
lean_inc(v_toBind_2938_);
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_2946_, 0, v_toPure_2939_);
lean_closure_set(v___f_2946_, 1, v_x_2940_);
lean_closure_set(v___f_2946_, 2, v_toBind_2938_);
lean_closure_set(v___f_2946_, 3, v_inst_2926_);
lean_closure_set(v___f_2946_, 4, v_inst_2927_);
lean_closure_set(v___f_2946_, 5, v_inst_2928_);
lean_closure_set(v___f_2946_, 6, v_pre_2931_);
lean_closure_set(v___f_2946_, 7, v_post_2932_);
lean_closure_set(v___f_2946_, 8, v___x_2943_);
lean_closure_set(v___f_2946_, 9, v___x_2944_);
lean_closure_set(v___f_2946_, 10, v___x_2945_);
lean_closure_set(v___f_2946_, 11, v_x_2936_);
lean_closure_set(v___f_2946_, 12, v_input_2929_);
v___x_2947_ = lean_apply_4(v_toBind_2938_, lean_box(0), lean_box(0), v___x_2942_, v___f_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_input_2952_, lean_object* v_cache_2953_, lean_object* v_pre_2954_, lean_object* v_post_2955_, lean_object* v_usedLetOnly_2956_, lean_object* v_skipConstInApp_2957_, lean_object* v_skipInstances_2958_){
_start:
{
uint8_t v_usedLetOnly_boxed_2959_; uint8_t v_skipConstInApp_boxed_2960_; uint8_t v_skipInstances_boxed_2961_; lean_object* v_res_2962_; 
v_usedLetOnly_boxed_2959_ = lean_unbox(v_usedLetOnly_2956_);
v_skipConstInApp_boxed_2960_ = lean_unbox(v_skipConstInApp_2957_);
v_skipInstances_boxed_2961_ = lean_unbox(v_skipInstances_2958_);
v_res_2962_ = l_Lean_Meta_transformWithCache(v_m_2948_, v_inst_2949_, v_inst_2950_, v_inst_2951_, v_input_2952_, v_cache_2953_, v_pre_2954_, v_post_2955_, v_usedLetOnly_boxed_2959_, v_skipConstInApp_boxed_2960_, v_skipInstances_boxed_2961_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_2963_, lean_object* v_x_2964_, lean_object* v_toBind_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_pre_2969_, lean_object* v_post_2970_, uint8_t v_usedLetOnly_2971_, uint8_t v_skipConstInApp_2972_, uint8_t v___x_2973_, lean_object* v_x_2974_, lean_object* v_input_2975_, lean_object* v_ref_2976_){
_start:
{
lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_inc(v_toBind_2965_);
lean_inc(v_x_2964_);
lean_inc(v_ref_2976_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2977_, 0, v_toPure_2963_);
lean_closure_set(v___f_2977_, 1, v_ref_2976_);
lean_closure_set(v___f_2977_, 2, v_x_2964_);
lean_closure_set(v___f_2977_, 3, v_toBind_2965_);
v___x_2978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2966_, v_inst_2967_, v_inst_2968_, v_pre_2969_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v___x_2973_, v_x_2974_, v_x_2964_, v_input_2975_, v_ref_2976_);
v___x_2979_ = lean_apply_4(v_toBind_2965_, lean_box(0), lean_box(0), v___x_2978_, v___f_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_2980_, lean_object* v_x_2981_, lean_object* v_toBind_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_pre_2986_, lean_object* v_post_2987_, lean_object* v_usedLetOnly_2988_, lean_object* v_skipConstInApp_2989_, lean_object* v___x_2990_, lean_object* v_x_2991_, lean_object* v_input_2992_, lean_object* v_ref_2993_){
_start:
{
uint8_t v_usedLetOnly_boxed_2994_; uint8_t v_skipConstInApp_boxed_2995_; uint8_t v___x_114__boxed_2996_; lean_object* v_res_2997_; 
v_usedLetOnly_boxed_2994_ = lean_unbox(v_usedLetOnly_2988_);
v_skipConstInApp_boxed_2995_ = lean_unbox(v_skipConstInApp_2989_);
v___x_114__boxed_2996_ = lean_unbox(v___x_2990_);
v_res_2997_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_2980_, v_x_2981_, v_toBind_2982_, v_inst_2983_, v_inst_2984_, v_inst_2985_, v_pre_2986_, v_post_2987_, v_usedLetOnly_boxed_2994_, v_skipConstInApp_boxed_2995_, v___x_114__boxed_2996_, v_x_2991_, v_input_2992_, v_ref_2993_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_input_3001_, lean_object* v_pre_3002_, lean_object* v_post_3003_, uint8_t v_usedLetOnly_3004_, uint8_t v_skipConstInApp_3005_){
_start:
{
lean_object* v_toApplicative_3006_; lean_object* v_toBind_3007_; lean_object* v_x_3008_; lean_object* v_toPure_3009_; lean_object* v_x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_toApplicative_3006_ = lean_ctor_get(v_inst_2998_, 0);
v_toBind_3007_ = lean_ctor_get(v_inst_2998_, 1);
lean_inc(v_toBind_3007_);
v_x_3008_ = lean_box(0);
v_toPure_3009_ = lean_ctor_get(v_toApplicative_3006_, 1);
lean_inc(v_toPure_3009_);
lean_inc(v_inst_2999_);
v_x_3010_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3010_, 0, v_inst_2999_);
v___x_3011_ = 0;
v___x_3012_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
lean_inc(v_inst_2999_);
v___x_3013_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_2999_, lean_box(0), v___x_3012_);
lean_inc(v_toPure_3009_);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3014_, 0, v_toPure_3009_);
v___x_3015_ = lean_box(v_usedLetOnly_3004_);
v___x_3016_ = lean_box(v_skipConstInApp_3005_);
v___x_3017_ = lean_box(v___x_3011_);
lean_inc(v_toBind_3007_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3018_, 0, v_toPure_3009_);
lean_closure_set(v___f_3018_, 1, v_x_3010_);
lean_closure_set(v___f_3018_, 2, v_toBind_3007_);
lean_closure_set(v___f_3018_, 3, v_inst_2998_);
lean_closure_set(v___f_3018_, 4, v_inst_2999_);
lean_closure_set(v___f_3018_, 5, v_inst_3000_);
lean_closure_set(v___f_3018_, 6, v_pre_3002_);
lean_closure_set(v___f_3018_, 7, v_post_3003_);
lean_closure_set(v___f_3018_, 8, v___x_3015_);
lean_closure_set(v___f_3018_, 9, v___x_3016_);
lean_closure_set(v___f_3018_, 10, v___x_3017_);
lean_closure_set(v___f_3018_, 11, v_x_3008_);
lean_closure_set(v___f_3018_, 12, v_input_3001_);
lean_inc(v_toBind_3007_);
v___x_3019_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3013_, v___f_3018_);
v___x_3020_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3019_, v___f_3014_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_input_3024_, lean_object* v_pre_3025_, lean_object* v_post_3026_, lean_object* v_usedLetOnly_3027_, lean_object* v_skipConstInApp_3028_){
_start:
{
uint8_t v_usedLetOnly_boxed_3029_; uint8_t v_skipConstInApp_boxed_3030_; lean_object* v_res_3031_; 
v_usedLetOnly_boxed_3029_ = lean_unbox(v_usedLetOnly_3027_);
v_skipConstInApp_boxed_3030_ = lean_unbox(v_skipConstInApp_3028_);
v_res_3031_ = l_Lean_Meta_transform___redArg(v_inst_3021_, v_inst_3022_, v_inst_3023_, v_input_3024_, v_pre_3025_, v_post_3026_, v_usedLetOnly_boxed_3029_, v_skipConstInApp_boxed_3030_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_input_3036_, lean_object* v_pre_3037_, lean_object* v_post_3038_, uint8_t v_usedLetOnly_3039_, uint8_t v_skipConstInApp_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Meta_transform___redArg(v_inst_3033_, v_inst_3034_, v_inst_3035_, v_input_3036_, v_pre_3037_, v_post_3038_, v_usedLetOnly_3039_, v_skipConstInApp_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3042_, lean_object* v_inst_3043_, lean_object* v_inst_3044_, lean_object* v_inst_3045_, lean_object* v_input_3046_, lean_object* v_pre_3047_, lean_object* v_post_3048_, lean_object* v_usedLetOnly_3049_, lean_object* v_skipConstInApp_3050_){
_start:
{
uint8_t v_usedLetOnly_boxed_3051_; uint8_t v_skipConstInApp_boxed_3052_; lean_object* v_res_3053_; 
v_usedLetOnly_boxed_3051_ = lean_unbox(v_usedLetOnly_3049_);
v_skipConstInApp_boxed_3052_ = lean_unbox(v_skipConstInApp_3050_);
v_res_3053_ = l_Lean_Meta_transform(v_m_3042_, v_inst_3043_, v_inst_3044_, v_inst_3045_, v_input_3046_, v_pre_3047_, v_post_3048_, v_usedLetOnly_boxed_3051_, v_skipConstInApp_boxed_3052_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v___x_3057_; 
v___x_3057_ = l_Lean_Expr_hasMVar(v_e_3054_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_e_3054_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v_mctx_3060_; lean_object* v___x_3061_; lean_object* v_fst_3062_; lean_object* v_snd_3063_; lean_object* v___x_3064_; lean_object* v_cache_3065_; lean_object* v_zetaDeltaFVarIds_3066_; lean_object* v_postponed_3067_; lean_object* v_diag_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3077_; 
v___x_3059_ = lean_st_ref_get(v___y_3055_);
v_mctx_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc_ref(v_mctx_3060_);
lean_dec(v___x_3059_);
v___x_3061_ = l_Lean_instantiateMVarsCore(v_mctx_3060_, v_e_3054_);
v_fst_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_fst_3062_);
v_snd_3063_ = lean_ctor_get(v___x_3061_, 1);
lean_inc(v_snd_3063_);
lean_dec_ref(v___x_3061_);
v___x_3064_ = lean_st_ref_take(v___y_3055_);
v_cache_3065_ = lean_ctor_get(v___x_3064_, 1);
v_zetaDeltaFVarIds_3066_ = lean_ctor_get(v___x_3064_, 2);
v_postponed_3067_ = lean_ctor_get(v___x_3064_, 3);
v_diag_3068_ = lean_ctor_get(v___x_3064_, 4);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3064_, 0);
lean_dec(v_unused_3078_);
v___x_3070_ = v___x_3064_;
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_diag_3068_);
lean_inc(v_postponed_3067_);
lean_inc(v_zetaDeltaFVarIds_3066_);
lean_inc(v_cache_3065_);
lean_dec(v___x_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v_snd_3063_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_snd_3063_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_cache_3065_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_zetaDeltaFVarIds_3066_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_postponed_3067_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_diag_3068_);
v___x_3073_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_st_ref_set(v___y_3055_, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v_fst_3062_);
return v___x_3075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3079_, v___y_3080_);
lean_dec(v___y_3080_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3083_, v___y_3085_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3097_, lean_object* v___x_3098_, uint8_t v_zetaDelta_3099_, lean_object* v_fvarId_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3135_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3135_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3135_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
if (lean_obj_tag(v_a_3107_) == 1)
{
lean_object* v_val_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3130_; 
v_val_3111_ = lean_ctor_get(v_a_3107_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3107_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3113_ = v_a_3107_;
v_isShared_3114_ = v_isSharedCheck_3130_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_val_3111_);
lean_dec(v_a_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3130_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
uint8_t v___y_3116_; 
if (v_zetaDelta_3099_ == 0)
{
lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = l_Lean_LocalDecl_index(v_val_3111_);
v___x_3125_ = lean_nat_dec_lt(v___x_3124_, v___x_3098_);
lean_dec(v___x_3124_);
if (v___x_3125_ == 0)
{
lean_del_object(v___x_3113_);
goto v___jp_3121_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec(v_val_3111_);
lean_del_object(v___x_3109_);
v___x_3126_ = lean_box(0);
if (v_isShared_3114_ == 0)
{
lean_ctor_set_tag(v___x_3113_, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3126_);
v___x_3128_ = v___x_3113_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_del_object(v___x_3113_);
goto v___jp_3121_;
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = l_Lean_LocalDecl_value_x3f(v_val_3111_, v___y_3116_);
lean_dec(v_val_3111_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3117_);
v___x_3119_ = v___x_3109_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
v___jp_3121_:
{
if (v_zetaHave_3097_ == 0)
{
v___y_3116_ = v_zetaHave_3097_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = l_Lean_LocalDecl_index(v_val_3111_);
v___x_3123_ = lean_nat_dec_le(v___x_3098_, v___x_3122_);
lean_dec(v___x_3122_);
v___y_3116_ = v___x_3123_;
goto v___jp_3115_;
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec(v_a_3107_);
v___x_3131_ = lean_box(0);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3131_);
v___x_3133_ = v___x_3109_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3106_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3106_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3144_, lean_object* v___x_3145_, lean_object* v_zetaDelta_3146_, lean_object* v_fvarId_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v_zetaHave_boxed_3153_; uint8_t v_zetaDelta_boxed_3154_; lean_object* v_res_3155_; 
v_zetaHave_boxed_3153_ = lean_unbox(v_zetaHave_3144_);
v_zetaDelta_boxed_3154_ = lean_unbox(v_zetaDelta_3146_);
v_res_3155_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3153_, v___x_3145_, v_zetaDelta_boxed_3154_, v_fvarId_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___x_3145_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_e_3156_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3171_, lean_object* v_e_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
if (lean_obj_tag(v_e_3172_) == 1)
{
lean_object* v_fvarId_3178_; lean_object* v___x_3179_; 
v_fvarId_3178_ = lean_ctor_get(v_e_3172_, 0);
lean_inc(v___y_3174_);
lean_inc(v_fvarId_3178_);
v___x_3179_ = lean_apply_6(v___f_3171_, v_fvarId_3178_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, lean_box(0));
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3205_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3205_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3205_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
if (lean_obj_tag(v_a_3180_) == 1)
{
lean_object* v_val_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3200_; 
lean_del_object(v___x_3182_);
lean_dec_ref(v_e_3172_);
v_val_3184_ = lean_ctor_get(v_a_3180_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_a_3180_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3186_ = v_a_3180_;
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_val_3184_);
lean_dec(v_a_3180_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3199_; 
v___x_3188_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3184_, v___y_3174_);
lean_dec(v___y_3174_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3199_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3199_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_a_3189_);
v___x_3194_ = v___x_3186_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3194_);
v___x_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_dec(v_a_3180_);
lean_dec(v___y_3174_);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_e_3172_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3201_);
v___x_3203_ = v___x_3182_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v_e_3172_);
lean_dec(v___y_3174_);
v_a_3206_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3179_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3179_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_e_3172_);
lean_dec_ref(v___f_3171_);
v___x_3214_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3216_, lean_object* v_e_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3216_, v_e_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3224_, lean_object* v_e_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Expr_getAppFn(v_e_3225_);
if (lean_obj_tag(v___x_3231_) == 1)
{
lean_object* v_fvarId_3232_; lean_object* v___x_3233_; 
v_fvarId_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_fvarId_3232_);
lean_dec_ref(v___x_3231_);
lean_inc(v___y_3227_);
v___x_3233_ = lean_apply_6(v___f_3224_, v_fvarId_3232_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, lean_box(0));
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3266_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3266_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3266_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
if (lean_obj_tag(v_a_3234_) == 1)
{
lean_object* v_val_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3261_; 
lean_del_object(v___x_3236_);
v_val_3238_ = lean_ctor_get(v_a_3234_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3240_ = v_a_3234_;
v_isShared_3241_ = v_isSharedCheck_3261_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_val_3238_);
lean_dec(v_a_3234_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3261_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3260_; 
v___x_3242_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3238_, v___y_3227_);
lean_dec(v___y_3227_);
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3260_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3260_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_dummy_3247_; lean_object* v_nargs_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
v_dummy_3247_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3248_ = l_Lean_Expr_getAppNumArgs(v_e_3225_);
lean_inc(v_nargs_3248_);
v___x_3249_ = lean_mk_array(v_nargs_3248_, v_dummy_3247_);
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_nat_sub(v_nargs_3248_, v___x_3250_);
lean_dec(v_nargs_3248_);
v___x_3252_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3225_, v___x_3249_, v___x_3251_);
v___x_3253_ = l_Lean_Expr_beta(v_a_3243_, v___x_3252_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3253_);
v___x_3255_ = v___x_3240_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3255_);
v___x_3257_ = v___x_3245_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_dec(v_a_3234_);
lean_dec(v___y_3227_);
lean_dec_ref(v_e_3225_);
v___x_3262_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3262_);
v___x_3264_ = v___x_3236_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v___y_3227_);
lean_dec_ref(v_e_3225_);
v_a_3267_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3233_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3233_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec_ref(v___x_3231_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v_e_3225_);
lean_dec_ref(v___f_3224_);
v___x_3275_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3277_, lean_object* v_e_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3277_, v_e_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_apply_1(v_x_3286_, lean_box(0));
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3294_, v_x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3302_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3316_, lean_object* v___y_3317_, lean_object* v_b_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_apply_7(v_k_3316_, v_b_3318_, v___y_3317_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, lean_box(0));
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3325_, lean_object* v___y_3326_, lean_object* v_b_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3325_, v___y_3326_, v_b_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3334_, uint8_t v_bi_3335_, lean_object* v_type_3336_, lean_object* v_k_3337_, uint8_t v_kind_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___f_3345_; lean_object* v___x_3346_; 
v___f_3345_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3345_, 0, v_k_3337_);
lean_closure_set(v___f_3345_, 1, v___y_3339_);
v___x_3346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3334_, v_bi_3335_, v_type_3336_, v___f_3345_, v_kind_3338_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3346_) == 0)
{
return v___x_3346_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3355_, lean_object* v_bi_3356_, lean_object* v_type_3357_, lean_object* v_k_3358_, lean_object* v_kind_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v_bi_boxed_3366_; uint8_t v_kind_boxed_3367_; lean_object* v_res_3368_; 
v_bi_boxed_3366_ = lean_unbox(v_bi_3356_);
v_kind_boxed_3367_ = lean_unbox(v_kind_3359_);
v_res_3368_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3355_, v_bi_boxed_3366_, v_type_3357_, v_k_3358_, v_kind_boxed_3367_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3369_, lean_object* v_type_3370_, lean_object* v_val_3371_, lean_object* v_k_3372_, uint8_t v_nondep_3373_, uint8_t v_kind_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___f_3381_; lean_object* v___x_3382_; 
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3381_, 0, v_k_3372_);
lean_closure_set(v___f_3381_, 1, v___y_3375_);
v___x_3382_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3369_, v_type_3370_, v_val_3371_, v___f_3381_, v_nondep_3373_, v_kind_3374_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3382_) == 0)
{
return v___x_3382_;
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3391_, lean_object* v_type_3392_, lean_object* v_val_3393_, lean_object* v_k_3394_, lean_object* v_nondep_3395_, lean_object* v_kind_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v_nondep_boxed_3403_; uint8_t v_kind_boxed_3404_; lean_object* v_res_3405_; 
v_nondep_boxed_3403_ = lean_unbox(v_nondep_3395_);
v_kind_boxed_3404_ = lean_unbox(v_kind_3396_);
v_res_3405_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3391_, v_type_3392_, v_val_3393_, v_k_3394_, v_nondep_boxed_3403_, v_kind_boxed_3404_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_apply_1(v_x_3407_, lean_box(0));
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3415_, v_x_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3423_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v_ref_3423_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___y_3439_; lean_object* v_fileName_3448_; lean_object* v_fileMap_3449_; lean_object* v_options_3450_; lean_object* v_currRecDepth_3451_; lean_object* v_maxRecDepth_3452_; lean_object* v_ref_3453_; lean_object* v_currNamespace_3454_; lean_object* v_openDecls_3455_; lean_object* v_initHeartbeats_3456_; lean_object* v_maxHeartbeats_3457_; lean_object* v_quotContext_3458_; lean_object* v_currMacroScope_3459_; uint8_t v_diag_3460_; lean_object* v_cancelTk_x3f_3461_; uint8_t v_suppressElabErrors_3462_; lean_object* v_inheritedTraceOptions_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3475_; 
v_fileName_3448_ = lean_ctor_get(v___y_3435_, 0);
v_fileMap_3449_ = lean_ctor_get(v___y_3435_, 1);
v_options_3450_ = lean_ctor_get(v___y_3435_, 2);
v_currRecDepth_3451_ = lean_ctor_get(v___y_3435_, 3);
v_maxRecDepth_3452_ = lean_ctor_get(v___y_3435_, 4);
v_ref_3453_ = lean_ctor_get(v___y_3435_, 5);
v_currNamespace_3454_ = lean_ctor_get(v___y_3435_, 6);
v_openDecls_3455_ = lean_ctor_get(v___y_3435_, 7);
v_initHeartbeats_3456_ = lean_ctor_get(v___y_3435_, 8);
v_maxHeartbeats_3457_ = lean_ctor_get(v___y_3435_, 9);
v_quotContext_3458_ = lean_ctor_get(v___y_3435_, 10);
v_currMacroScope_3459_ = lean_ctor_get(v___y_3435_, 11);
v_diag_3460_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*14);
v_cancelTk_x3f_3461_ = lean_ctor_get(v___y_3435_, 12);
v_suppressElabErrors_3462_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3463_ = lean_ctor_get(v___y_3435_, 13);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___y_3435_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3465_ = v___y_3435_;
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_inheritedTraceOptions_3463_);
lean_inc(v_cancelTk_x3f_3461_);
lean_inc(v_currMacroScope_3459_);
lean_inc(v_quotContext_3458_);
lean_inc(v_maxHeartbeats_3457_);
lean_inc(v_initHeartbeats_3456_);
lean_inc(v_openDecls_3455_);
lean_inc(v_currNamespace_3454_);
lean_inc(v_ref_3453_);
lean_inc(v_maxRecDepth_3452_);
lean_inc(v_currRecDepth_3451_);
lean_inc(v_options_3450_);
lean_inc(v_fileMap_3449_);
lean_inc(v_fileName_3448_);
lean_dec(v___y_3435_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
v___jp_3438_:
{
if (lean_obj_tag(v___y_3439_) == 0)
{
return v___y_3439_;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
v_a_3440_ = lean_ctor_get(v___y_3439_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___y_3439_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___y_3439_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___y_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
v_resetjp_3464_:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_nat_dec_eq(v_currRecDepth_3451_, v_maxRecDepth_3452_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_nat_add(v_currRecDepth_3451_, v___x_3468_);
lean_dec(v_currRecDepth_3451_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 3, v___x_3469_);
v___x_3471_ = v___x_3465_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_fileName_3448_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_fileMap_3449_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_options_3450_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_maxRecDepth_3452_);
lean_ctor_set(v_reuseFailAlloc_3473_, 5, v_ref_3453_);
lean_ctor_set(v_reuseFailAlloc_3473_, 6, v_currNamespace_3454_);
lean_ctor_set(v_reuseFailAlloc_3473_, 7, v_openDecls_3455_);
lean_ctor_set(v_reuseFailAlloc_3473_, 8, v_initHeartbeats_3456_);
lean_ctor_set(v_reuseFailAlloc_3473_, 9, v_maxHeartbeats_3457_);
lean_ctor_set(v_reuseFailAlloc_3473_, 10, v_quotContext_3458_);
lean_ctor_set(v_reuseFailAlloc_3473_, 11, v_currMacroScope_3459_);
lean_ctor_set(v_reuseFailAlloc_3473_, 12, v_cancelTk_x3f_3461_);
lean_ctor_set(v_reuseFailAlloc_3473_, 13, v_inheritedTraceOptions_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3473_, sizeof(void*)*14, v_diag_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3473_, sizeof(void*)*14 + 1, v_suppressElabErrors_3462_);
v___x_3471_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_apply_6(v_x_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___x_3471_, v___y_3436_, lean_box(0));
v___y_3439_ = v___x_3472_;
goto v___jp_3438_;
}
}
else
{
lean_object* v___x_3474_; 
lean_del_object(v___x_3465_);
lean_dec_ref(v_inheritedTraceOptions_3463_);
lean_dec(v_cancelTk_x3f_3461_);
lean_dec(v_currMacroScope_3459_);
lean_dec(v_quotContext_3458_);
lean_dec(v_maxHeartbeats_3457_);
lean_dec(v_initHeartbeats_3456_);
lean_dec(v_openDecls_3455_);
lean_dec(v_currNamespace_3454_);
lean_dec(v_maxRecDepth_3452_);
lean_dec(v_currRecDepth_3451_);
lean_dec_ref(v_options_3450_);
lean_dec_ref(v_fileMap_3449_);
lean_dec_ref(v_fileName_3448_);
lean_dec(v___y_3436_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v_x_3431_);
v___x_3474_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3453_);
v___y_3439_ = v___x_3474_;
goto v___jp_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3484_, lean_object* v_pre_3485_, lean_object* v_post_3486_, uint8_t v_usedLetOnly_3487_, uint8_t v_skipConstInApp_3488_, uint8_t v_skipInstances_3489_, lean_object* v_body_3490_, lean_object* v_x_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_array_push(v_fvars_3484_, v_x_3491_);
v___x_3499_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3485_, v_post_3486_, v_usedLetOnly_3487_, v_skipConstInApp_3488_, v_skipInstances_3489_, v___x_3498_, v_body_3490_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3500_, lean_object* v_pre_3501_, lean_object* v_post_3502_, lean_object* v_usedLetOnly_3503_, lean_object* v_skipConstInApp_3504_, lean_object* v_skipInstances_3505_, lean_object* v_body_3506_, lean_object* v_x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_usedLetOnly_boxed_3514_; uint8_t v_skipConstInApp_boxed_3515_; uint8_t v_skipInstances_boxed_3516_; lean_object* v_res_3517_; 
v_usedLetOnly_boxed_3514_ = lean_unbox(v_usedLetOnly_3503_);
v_skipConstInApp_boxed_3515_ = lean_unbox(v_skipConstInApp_3504_);
v_skipInstances_boxed_3516_ = lean_unbox(v_skipInstances_3505_);
v_res_3517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3500_, v_pre_3501_, v_post_3502_, v_usedLetOnly_boxed_3514_, v_skipConstInApp_boxed_3515_, v_skipInstances_boxed_3516_, v_body_3506_, v_x_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3518_, lean_object* v_post_3519_, uint8_t v_usedLetOnly_3520_, uint8_t v_skipConstInApp_3521_, uint8_t v_skipInstances_3522_, lean_object* v_e_3523_, lean_object* v_a_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
lean_inc_ref(v_post_3519_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc(v___y_3526_);
lean_inc_ref(v___y_3525_);
lean_inc_ref(v_e_3523_);
v___x_3530_ = lean_apply_6(v_post_3519_, v_e_3523_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, lean_box(0));
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3549_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3549_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3549_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
switch(lean_obj_tag(v_a_3531_))
{
case 0:
{
lean_object* v_e_3535_; lean_object* v___x_3537_; 
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3523_);
lean_dec_ref(v_post_3519_);
lean_dec_ref(v_pre_3518_);
v_e_3535_ = lean_ctor_get(v_a_3531_, 0);
lean_inc_ref(v_e_3535_);
lean_dec_ref(v_a_3531_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_e_3535_);
v___x_3537_ = v___x_3533_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_e_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
case 1:
{
lean_object* v_e_3539_; lean_object* v___x_3540_; 
lean_del_object(v___x_3533_);
lean_dec_ref(v_e_3523_);
v_e_3539_ = lean_ctor_get(v_a_3531_, 0);
lean_inc_ref(v_e_3539_);
lean_dec_ref(v_a_3531_);
v___x_3540_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3518_, v_post_3519_, v_usedLetOnly_3520_, v_skipConstInApp_3521_, v_skipInstances_3522_, v_e_3539_, v_a_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
return v___x_3540_;
}
default: 
{
lean_object* v_e_x3f_3541_; 
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_post_3519_);
lean_dec_ref(v_pre_3518_);
v_e_x3f_3541_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_e_x3f_3541_);
lean_dec_ref(v_a_3531_);
if (lean_obj_tag(v_e_x3f_3541_) == 0)
{
lean_object* v___x_3543_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_e_3523_);
v___x_3543_ = v___x_3533_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_e_3523_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
else
{
lean_object* v_val_3545_; lean_object* v___x_3547_; 
lean_dec_ref(v_e_3523_);
v_val_3545_ = lean_ctor_get(v_e_x3f_3541_, 0);
lean_inc(v_val_3545_);
lean_dec_ref(v_e_x3f_3541_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_val_3545_);
v___x_3547_ = v___x_3533_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_val_3545_);
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
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3523_);
lean_dec_ref(v_post_3519_);
lean_dec_ref(v_pre_3518_);
v_a_3550_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3530_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3530_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3558_, lean_object* v_post_3559_, uint8_t v_usedLetOnly_3560_, uint8_t v_skipConstInApp_3561_, uint8_t v_skipInstances_3562_, lean_object* v_fvars_3563_, lean_object* v_e_3564_, lean_object* v_a_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
if (lean_obj_tag(v_e_3564_) == 6)
{
lean_object* v_binderName_3571_; lean_object* v_binderType_3572_; lean_object* v_body_3573_; uint8_t v_binderInfo_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_binderName_3571_ = lean_ctor_get(v_e_3564_, 0);
lean_inc(v_binderName_3571_);
v_binderType_3572_ = lean_ctor_get(v_e_3564_, 1);
lean_inc_ref(v_binderType_3572_);
v_body_3573_ = lean_ctor_get(v_e_3564_, 2);
lean_inc_ref(v_body_3573_);
v_binderInfo_3574_ = lean_ctor_get_uint8(v_e_3564_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3564_);
v___x_3575_ = lean_expr_instantiate_rev(v_binderType_3572_, v_fvars_3563_);
lean_dec_ref(v_binderType_3572_);
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_post_3559_);
lean_inc_ref(v_pre_3558_);
v___x_3576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3558_, v_post_3559_, v_usedLetOnly_3560_, v_skipConstInApp_3561_, v_skipInstances_3562_, v___x_3575_, v_a_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___f_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = lean_box(v_usedLetOnly_3560_);
v___x_3579_ = lean_box(v_skipConstInApp_3561_);
v___x_3580_ = lean_box(v_skipInstances_3562_);
v___f_3581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3581_, 0, v_fvars_3563_);
lean_closure_set(v___f_3581_, 1, v_pre_3558_);
lean_closure_set(v___f_3581_, 2, v_post_3559_);
lean_closure_set(v___f_3581_, 3, v___x_3578_);
lean_closure_set(v___f_3581_, 4, v___x_3579_);
lean_closure_set(v___f_3581_, 5, v___x_3580_);
lean_closure_set(v___f_3581_, 6, v_body_3573_);
v___x_3582_ = 0;
v___x_3583_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3571_, v_binderInfo_3574_, v_a_3577_, v___f_3581_, v___x_3582_, v_a_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
return v___x_3583_;
}
else
{
lean_dec_ref(v_body_3573_);
lean_dec(v_binderName_3571_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_fvars_3563_);
lean_dec_ref(v_post_3559_);
lean_dec_ref(v_pre_3558_);
return v___x_3576_;
}
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_expr_instantiate_rev(v_e_3564_, v_fvars_3563_);
lean_dec_ref(v_e_3564_);
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
lean_inc(v_a_3565_);
lean_inc_ref(v_post_3559_);
lean_inc_ref(v_pre_3558_);
v___x_3585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3558_, v_post_3559_, v_usedLetOnly_3560_, v_skipConstInApp_3561_, v_skipInstances_3562_, v___x_3584_, v_a_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; uint8_t v___x_3587_; uint8_t v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v___x_3585_);
v___x_3587_ = 0;
v___x_3588_ = 1;
v___x_3589_ = 1;
v___x_3590_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3563_, v_a_3586_, v___x_3587_, v_usedLetOnly_3560_, v___x_3587_, v___x_3588_, v___x_3589_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec_ref(v_fvars_3563_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3558_, v_post_3559_, v_usedLetOnly_3560_, v_skipConstInApp_3561_, v_skipInstances_3562_, v_a_3591_, v_a_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
return v___x_3592_;
}
else
{
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_post_3559_);
lean_dec_ref(v_pre_3558_);
return v___x_3590_;
}
}
else
{
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_fvars_3563_);
lean_dec_ref(v_post_3559_);
lean_dec_ref(v_pre_3558_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3593_, lean_object* v_pre_3594_, lean_object* v_post_3595_, uint8_t v_usedLetOnly_3596_, uint8_t v_skipConstInApp_3597_, uint8_t v_skipInstances_3598_, lean_object* v_body_3599_, lean_object* v_x_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_array_push(v_fvars_3593_, v_x_3600_);
v___x_3608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3594_, v_post_3595_, v_usedLetOnly_3596_, v_skipConstInApp_3597_, v_skipInstances_3598_, v___x_3607_, v_body_3599_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3609_, lean_object* v_pre_3610_, lean_object* v_post_3611_, lean_object* v_usedLetOnly_3612_, lean_object* v_skipConstInApp_3613_, lean_object* v_skipInstances_3614_, lean_object* v_body_3615_, lean_object* v_x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
uint8_t v_usedLetOnly_boxed_3623_; uint8_t v_skipConstInApp_boxed_3624_; uint8_t v_skipInstances_boxed_3625_; lean_object* v_res_3626_; 
v_usedLetOnly_boxed_3623_ = lean_unbox(v_usedLetOnly_3612_);
v_skipConstInApp_boxed_3624_ = lean_unbox(v_skipConstInApp_3613_);
v_skipInstances_boxed_3625_ = lean_unbox(v_skipInstances_3614_);
v_res_3626_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3609_, v_pre_3610_, v_post_3611_, v_usedLetOnly_boxed_3623_, v_skipConstInApp_boxed_3624_, v_skipInstances_boxed_3625_, v_body_3615_, v_x_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3627_, lean_object* v_post_3628_, uint8_t v_usedLetOnly_3629_, uint8_t v_skipConstInApp_3630_, uint8_t v_skipInstances_3631_, lean_object* v_fvars_3632_, lean_object* v_e_3633_, lean_object* v_a_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
if (lean_obj_tag(v_e_3633_) == 8)
{
lean_object* v_declName_3640_; lean_object* v_type_3641_; lean_object* v_value_3642_; lean_object* v_body_3643_; uint8_t v_nondep_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_declName_3640_ = lean_ctor_get(v_e_3633_, 0);
lean_inc(v_declName_3640_);
v_type_3641_ = lean_ctor_get(v_e_3633_, 1);
lean_inc_ref(v_type_3641_);
v_value_3642_ = lean_ctor_get(v_e_3633_, 2);
lean_inc_ref(v_value_3642_);
v_body_3643_ = lean_ctor_get(v_e_3633_, 3);
lean_inc_ref(v_body_3643_);
v_nondep_3644_ = lean_ctor_get_uint8(v_e_3633_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3633_);
v___x_3645_ = lean_expr_instantiate_rev(v_type_3641_, v_fvars_3632_);
lean_dec_ref(v_type_3641_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v_a_3634_);
lean_inc_ref(v_post_3628_);
lean_inc_ref(v_pre_3627_);
v___x_3646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3627_, v_post_3628_, v_usedLetOnly_3629_, v_skipConstInApp_3630_, v_skipInstances_3631_, v___x_3645_, v_a_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref(v___x_3646_);
v___x_3648_ = lean_expr_instantiate_rev(v_value_3642_, v_fvars_3632_);
lean_dec_ref(v_value_3642_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v_a_3634_);
lean_inc_ref(v_post_3628_);
lean_inc_ref(v_pre_3627_);
v___x_3649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3627_, v_post_3628_, v_usedLetOnly_3629_, v_skipConstInApp_3630_, v_skipInstances_3631_, v___x_3648_, v_a_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___f_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref(v___x_3649_);
v___x_3651_ = lean_box(v_usedLetOnly_3629_);
v___x_3652_ = lean_box(v_skipConstInApp_3630_);
v___x_3653_ = lean_box(v_skipInstances_3631_);
v___f_3654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3654_, 0, v_fvars_3632_);
lean_closure_set(v___f_3654_, 1, v_pre_3627_);
lean_closure_set(v___f_3654_, 2, v_post_3628_);
lean_closure_set(v___f_3654_, 3, v___x_3651_);
lean_closure_set(v___f_3654_, 4, v___x_3652_);
lean_closure_set(v___f_3654_, 5, v___x_3653_);
lean_closure_set(v___f_3654_, 6, v_body_3643_);
v___x_3655_ = 0;
v___x_3656_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3640_, v_a_3647_, v_a_3650_, v___f_3654_, v_nondep_3644_, v___x_3655_, v_a_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v___x_3656_;
}
else
{
lean_dec(v_a_3647_);
lean_dec_ref(v_body_3643_);
lean_dec(v_declName_3640_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_fvars_3632_);
lean_dec_ref(v_post_3628_);
lean_dec_ref(v_pre_3627_);
return v___x_3649_;
}
}
else
{
lean_dec_ref(v_body_3643_);
lean_dec_ref(v_value_3642_);
lean_dec(v_declName_3640_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_fvars_3632_);
lean_dec_ref(v_post_3628_);
lean_dec_ref(v_pre_3627_);
return v___x_3646_;
}
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_expr_instantiate_rev(v_e_3633_, v_fvars_3632_);
lean_dec_ref(v_e_3633_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v_a_3634_);
lean_inc_ref(v_post_3628_);
lean_inc_ref(v_pre_3627_);
v___x_3658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3627_, v_post_3628_, v_usedLetOnly_3629_, v_skipConstInApp_3630_, v_skipInstances_3631_, v___x_3657_, v_a_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; uint8_t v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = 0;
v___x_3661_ = 1;
v___x_3662_ = l_Lean_Meta_mkLetFVars(v_fvars_3632_, v_a_3659_, v_usedLetOnly_3629_, v___x_3660_, v___x_3661_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec_ref(v_fvars_3632_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
v___x_3664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3627_, v_post_3628_, v_usedLetOnly_3629_, v_skipConstInApp_3630_, v_skipInstances_3631_, v_a_3663_, v_a_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v___x_3664_;
}
else
{
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_post_3628_);
lean_dec_ref(v_pre_3627_);
return v___x_3662_;
}
}
else
{
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_fvars_3632_);
lean_dec_ref(v_post_3628_);
lean_dec_ref(v_pre_3627_);
return v___x_3658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3665_, lean_object* v_post_3666_, uint8_t v_usedLetOnly_3667_, uint8_t v_skipConstInApp_3668_, uint8_t v_skipInstances_3669_, size_t v_sz_3670_, size_t v_i_3671_, lean_object* v_bs_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_usize_dec_lt(v_i_3671_, v_sz_3670_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v_post_3666_);
lean_dec_ref(v_pre_3665_);
v___x_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_bs_3672_);
return v___x_3680_;
}
else
{
lean_object* v_v_3681_; lean_object* v___x_3682_; 
v_v_3681_ = lean_array_uget_borrowed(v_bs_3672_, v_i_3671_);
lean_inc(v___y_3677_);
lean_inc_ref(v___y_3676_);
lean_inc(v___y_3675_);
lean_inc_ref(v___y_3674_);
lean_inc(v___y_3673_);
lean_inc(v_v_3681_);
lean_inc_ref(v_post_3666_);
lean_inc_ref(v_pre_3665_);
v___x_3682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3665_, v_post_3666_, v_usedLetOnly_3667_, v_skipConstInApp_3668_, v_skipInstances_3669_, v_v_3681_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v_bs_x27_3685_; size_t v___x_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = lean_unsigned_to_nat(0u);
v_bs_x27_3685_ = lean_array_uset(v_bs_3672_, v_i_3671_, v___x_3684_);
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_add(v_i_3671_, v___x_3686_);
v___x_3688_ = lean_array_uset(v_bs_x27_3685_, v_i_3671_, v_a_3683_);
v_i_3671_ = v___x_3687_;
v_bs_3672_ = v___x_3688_;
goto _start;
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v_bs_3672_);
lean_dec_ref(v_post_3666_);
lean_dec_ref(v_pre_3665_);
v_a_3690_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3682_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3682_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3698_, lean_object* v_post_3699_, uint8_t v_usedLetOnly_3700_, uint8_t v_skipConstInApp_3701_, uint8_t v_skipInstances_3702_, lean_object* v___x_3703_, lean_object* v___y_3704_, lean_object* v_b_3705_, lean_object* v_a_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3698_, v_post_3699_, v_usedLetOnly_3700_, v_skipConstInApp_3701_, v_skipInstances_3702_, v___x_3703_, v___y_3704_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3717_ = lean_array_fset(v_b_3705_, v_a_3706_, v_a_3713_);
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3718_);
v___x_3720_ = v___x_3715_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_b_3705_);
v_a_3723_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3712_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3712_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3731_, lean_object* v_post_3732_, lean_object* v_usedLetOnly_3733_, lean_object* v_skipConstInApp_3734_, lean_object* v_skipInstances_3735_, lean_object* v___x_3736_, lean_object* v___y_3737_, lean_object* v_b_3738_, lean_object* v_a_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
uint8_t v_usedLetOnly_boxed_3745_; uint8_t v_skipConstInApp_boxed_3746_; uint8_t v_skipInstances_boxed_3747_; lean_object* v_res_3748_; 
v_usedLetOnly_boxed_3745_ = lean_unbox(v_usedLetOnly_3733_);
v_skipConstInApp_boxed_3746_ = lean_unbox(v_skipConstInApp_3734_);
v_skipInstances_boxed_3747_ = lean_unbox(v_skipInstances_3735_);
v_res_3748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3731_, v_post_3732_, v_usedLetOnly_boxed_3745_, v_skipConstInApp_boxed_3746_, v_skipInstances_boxed_3747_, v___x_3736_, v___y_3737_, v_b_3738_, v_a_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v_a_3739_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3749_, lean_object* v___x_3750_, lean_object* v_pre_3751_, lean_object* v_post_3752_, uint8_t v_usedLetOnly_3753_, uint8_t v_skipConstInApp_3754_, uint8_t v_skipInstances_3755_, lean_object* v_a_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___y_3765_; uint8_t v___x_3788_; 
v___x_3788_ = lean_nat_dec_lt(v_a_3756_, v_upperBound_3749_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec(v_a_3756_);
lean_dec_ref(v_post_3752_);
lean_dec_ref(v_pre_3751_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_b_3757_);
return v___x_3789_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_array_fget_borrowed(v_b_3757_, v_a_3756_);
v___x_3791_ = lean_array_get_size(v___x_3750_);
v___x_3792_ = lean_nat_dec_lt(v_a_3756_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___f_3796_; 
lean_inc(v___x_3790_);
v___x_3793_ = lean_box(v_usedLetOnly_3753_);
v___x_3794_ = lean_box(v_skipConstInApp_3754_);
v___x_3795_ = lean_box(v_skipInstances_3755_);
lean_inc(v_a_3756_);
lean_inc(v___y_3758_);
lean_inc_ref(v_post_3752_);
lean_inc_ref(v_pre_3751_);
v___f_3796_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3796_, 0, v_pre_3751_);
lean_closure_set(v___f_3796_, 1, v_post_3752_);
lean_closure_set(v___f_3796_, 2, v___x_3793_);
lean_closure_set(v___f_3796_, 3, v___x_3794_);
lean_closure_set(v___f_3796_, 4, v___x_3795_);
lean_closure_set(v___f_3796_, 5, v___x_3790_);
lean_closure_set(v___f_3796_, 6, v___y_3758_);
lean_closure_set(v___f_3796_, 7, v_b_3757_);
lean_closure_set(v___f_3796_, 8, v_a_3756_);
v___y_3765_ = v___f_3796_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3797_; uint8_t v_isInstance_3798_; 
v___x_3797_ = lean_array_fget_borrowed(v___x_3750_, v_a_3756_);
v_isInstance_3798_ = lean_ctor_get_uint8(v___x_3797_, sizeof(void*)*1 + 4);
if (v_isInstance_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; 
lean_inc(v___x_3790_);
v___x_3799_ = lean_box(v_usedLetOnly_3753_);
v___x_3800_ = lean_box(v_skipConstInApp_3754_);
v___x_3801_ = lean_box(v_skipInstances_3755_);
lean_inc(v_a_3756_);
lean_inc(v___y_3758_);
lean_inc_ref(v_post_3752_);
lean_inc_ref(v_pre_3751_);
v___f_3802_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3802_, 0, v_pre_3751_);
lean_closure_set(v___f_3802_, 1, v_post_3752_);
lean_closure_set(v___f_3802_, 2, v___x_3799_);
lean_closure_set(v___f_3802_, 3, v___x_3800_);
lean_closure_set(v___f_3802_, 4, v___x_3801_);
lean_closure_set(v___f_3802_, 5, v___x_3790_);
lean_closure_set(v___f_3802_, 6, v___y_3758_);
lean_closure_set(v___f_3802_, 7, v_b_3757_);
lean_closure_set(v___f_3802_, 8, v_a_3756_);
v___y_3765_ = v___f_3802_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3803_; lean_object* v___f_3804_; 
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v_b_3757_);
v___f_3804_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3804_, 0, v___x_3803_);
v___y_3765_ = v___f_3804_;
goto v___jp_3764_;
}
}
}
v___jp_3764_:
{
lean_object* v___x_3766_; 
lean_inc(v___y_3762_);
lean_inc_ref(v___y_3761_);
lean_inc(v___y_3760_);
lean_inc_ref(v___y_3759_);
v___x_3766_ = lean_apply_5(v___y_3765_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, lean_box(0));
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3779_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3779_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3779_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
if (lean_obj_tag(v_a_3767_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec(v_a_3756_);
lean_dec_ref(v_post_3752_);
lean_dec_ref(v_pre_3751_);
v_a_3771_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v_a_3767_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_a_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_del_object(v___x_3769_);
v_a_3775_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v_a_3767_);
v___x_3776_ = lean_unsigned_to_nat(1u);
v___x_3777_ = lean_nat_add(v_a_3756_, v___x_3776_);
lean_dec(v_a_3756_);
v_a_3756_ = v___x_3777_;
v_b_3757_ = v_a_3775_;
goto _start;
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec(v_a_3756_);
lean_dec_ref(v_post_3752_);
lean_dec_ref(v_pre_3751_);
v_a_3780_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3766_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3766_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_3805_, lean_object* v_pre_3806_, lean_object* v_post_3807_, uint8_t v_usedLetOnly_3808_, uint8_t v_skipConstInApp_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_f_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; 
if (lean_obj_tag(v_x_3810_) == 5)
{
lean_object* v_fn_3868_; lean_object* v_arg_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_fn_3868_ = lean_ctor_get(v_x_3810_, 0);
lean_inc_ref(v_fn_3868_);
v_arg_3869_ = lean_ctor_get(v_x_3810_, 1);
lean_inc_ref(v_arg_3869_);
lean_dec_ref(v_x_3810_);
v___x_3870_ = lean_array_set(v_x_3811_, v_x_3812_, v_arg_3869_);
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = lean_nat_sub(v_x_3812_, v___x_3871_);
lean_dec(v_x_3812_);
v_x_3810_ = v_fn_3868_;
v_x_3811_ = v___x_3870_;
v_x_3812_ = v___x_3872_;
goto _start;
}
else
{
lean_dec(v_x_3812_);
if (v_skipConstInApp_3809_ == 0)
{
goto v___jp_3865_;
}
else
{
uint8_t v___x_3874_; 
v___x_3874_ = l_Lean_Expr_isConst(v_x_3810_);
if (v___x_3874_ == 0)
{
goto v___jp_3865_;
}
else
{
v_f_3820_ = v_x_3810_;
v___y_3821_ = v___y_3813_;
v___y_3822_ = v___y_3814_;
v___y_3823_ = v___y_3815_;
v___y_3824_ = v___y_3816_;
v___y_3825_ = v___y_3817_;
goto v___jp_3819_;
}
}
}
v___jp_3819_:
{
if (v_skipInstances_3805_ == 0)
{
size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v_sz_3826_ = lean_array_size(v_x_3811_);
v___x_3827_ = ((size_t)0ULL);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc(v___y_3821_);
lean_inc_ref(v_post_3807_);
lean_inc_ref(v_pre_3806_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_3806_, v_post_3807_, v_usedLetOnly_3808_, v_skipConstInApp_3809_, v_skipInstances_3805_, v_sz_3826_, v___x_3827_, v_x_3811_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = l_Lean_mkAppN(v_f_3820_, v_a_3829_);
lean_dec(v_a_3829_);
v___x_3831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3806_, v_post_3807_, v_usedLetOnly_3808_, v_skipConstInApp_3809_, v_skipInstances_3805_, v___x_3830_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v_f_3820_);
lean_dec_ref(v_post_3807_);
lean_dec_ref(v_pre_3806_);
v_a_3832_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3828_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3828_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_array_get_size(v_x_3811_);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc_ref(v_f_3820_);
v___x_3841_ = l_Lean_Meta_getFunInfoNArgs(v_f_3820_, v___x_3840_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v_paramInfo_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v___x_3841_);
v_paramInfo_3843_ = lean_ctor_get(v_a_3842_, 0);
lean_inc_ref(v_paramInfo_3843_);
lean_dec(v_a_3842_);
v___x_3844_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc(v___y_3821_);
lean_inc_ref(v_post_3807_);
lean_inc_ref(v_pre_3806_);
v___x_3845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_3840_, v_paramInfo_3843_, v_pre_3806_, v_post_3807_, v_usedLetOnly_3808_, v_skipConstInApp_3809_, v_skipInstances_3805_, v___x_3844_, v_x_3811_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec_ref(v_paramInfo_3843_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = l_Lean_mkAppN(v_f_3820_, v_a_3846_);
lean_dec(v_a_3846_);
v___x_3848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3806_, v_post_3807_, v_usedLetOnly_3808_, v_skipConstInApp_3809_, v_skipInstances_3805_, v___x_3847_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3848_;
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v_f_3820_);
lean_dec_ref(v_post_3807_);
lean_dec_ref(v_pre_3806_);
v_a_3849_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3845_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3845_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
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
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v_f_3820_);
lean_dec_ref(v_x_3811_);
lean_dec_ref(v_post_3807_);
lean_dec_ref(v_pre_3806_);
v_a_3857_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3841_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3841_);
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
v___jp_3865_:
{
lean_object* v___x_3866_; 
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
lean_inc_ref(v_post_3807_);
lean_inc_ref(v_pre_3806_);
v___x_3866_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3806_, v_post_3807_, v_usedLetOnly_3808_, v_skipConstInApp_3809_, v_skipInstances_3805_, v_x_3810_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v_f_3820_ = v_a_3867_;
v___y_3821_ = v___y_3813_;
v___y_3822_ = v___y_3814_;
v___y_3823_ = v___y_3815_;
v___y_3824_ = v___y_3816_;
v___y_3825_ = v___y_3817_;
goto v___jp_3819_;
}
else
{
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v_x_3811_);
lean_dec_ref(v_post_3807_);
lean_dec_ref(v_pre_3806_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v_pre_3875_, lean_object* v_e_3876_, lean_object* v_post_3877_, uint8_t v_usedLetOnly_3878_, uint8_t v_skipConstInApp_3879_, uint8_t v_skipInstances_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; 
lean_inc_ref(v_pre_3875_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc_ref(v_e_3876_);
v___x_3887_ = lean_apply_6(v_pre_3875_, v_e_3876_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, lean_box(0));
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3936_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3890_ = v___x_3887_;
v_isShared_3891_ = v_isSharedCheck_3936_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3936_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___y_3893_; 
switch(lean_obj_tag(v_a_3888_))
{
case 0:
{
lean_object* v_e_3928_; lean_object* v___x_3930_; 
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v_post_3877_);
lean_dec_ref(v_e_3876_);
lean_dec_ref(v_pre_3875_);
v_e_3928_ = lean_ctor_get(v_a_3888_, 0);
lean_inc_ref(v_e_3928_);
lean_dec_ref(v_a_3888_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v_e_3928_);
v___x_3930_ = v___x_3890_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_e_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
case 1:
{
lean_object* v_e_3932_; lean_object* v___x_3933_; 
lean_del_object(v___x_3890_);
lean_dec_ref(v_e_3876_);
v_e_3932_ = lean_ctor_get(v_a_3888_, 0);
lean_inc_ref(v_e_3932_);
lean_dec_ref(v_a_3888_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v_e_3932_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3933_;
}
default: 
{
lean_object* v_e_x3f_3934_; 
lean_del_object(v___x_3890_);
v_e_x3f_3934_ = lean_ctor_get(v_a_3888_, 0);
lean_inc(v_e_x3f_3934_);
lean_dec_ref(v_a_3888_);
if (lean_obj_tag(v_e_x3f_3934_) == 0)
{
v___y_3893_ = v_e_3876_;
goto v___jp_3892_;
}
else
{
lean_object* v_val_3935_; 
lean_dec_ref(v_e_3876_);
v_val_3935_ = lean_ctor_get(v_e_x3f_3934_, 0);
lean_inc(v_val_3935_);
lean_dec_ref(v_e_x3f_3934_);
v___y_3893_ = v_val_3935_;
goto v___jp_3892_;
}
}
}
v___jp_3892_:
{
switch(lean_obj_tag(v___y_3893_))
{
case 7:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___x_3894_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3895_;
}
case 6:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_3897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___x_3896_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3897_;
}
case 8:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_3899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___x_3898_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3899_;
}
case 5:
{
lean_object* v_dummy_3900_; lean_object* v_nargs_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_dummy_3900_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3901_ = l_Lean_Expr_getAppNumArgs(v___y_3893_);
lean_inc(v_nargs_3901_);
v___x_3902_ = lean_mk_array(v_nargs_3901_, v_dummy_3900_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_sub(v_nargs_3901_, v___x_3903_);
lean_dec(v_nargs_3901_);
v___x_3905_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_3880_, v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v___y_3893_, v___x_3902_, v___x_3904_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3905_;
}
case 10:
{
lean_object* v_data_3906_; lean_object* v_expr_3907_; lean_object* v___x_3908_; 
v_data_3906_ = lean_ctor_get(v___y_3893_, 0);
v_expr_3907_ = lean_ctor_get(v___y_3893_, 1);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v_expr_3907_);
lean_inc_ref(v_post_3877_);
lean_inc_ref(v_pre_3875_);
v___x_3908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v_expr_3907_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; size_t v___x_3910_; size_t v___x_3911_; uint8_t v___x_3912_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
v___x_3910_ = lean_ptr_addr(v_expr_3907_);
v___x_3911_ = lean_ptr_addr(v_a_3909_);
v___x_3912_ = lean_usize_dec_eq(v___x_3910_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_inc(v_data_3906_);
lean_dec_ref(v___y_3893_);
v___x_3913_ = l_Lean_Expr_mdata___override(v_data_3906_, v_a_3909_);
v___x_3914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___x_3913_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3914_;
}
else
{
lean_object* v___x_3915_; 
lean_dec(v_a_3909_);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3915_;
}
}
else
{
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v_post_3877_);
lean_dec_ref(v_pre_3875_);
return v___x_3908_;
}
}
case 11:
{
lean_object* v_typeName_3916_; lean_object* v_idx_3917_; lean_object* v_struct_3918_; lean_object* v___x_3919_; 
v_typeName_3916_ = lean_ctor_get(v___y_3893_, 0);
v_idx_3917_ = lean_ctor_get(v___y_3893_, 1);
v_struct_3918_ = lean_ctor_get(v___y_3893_, 2);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v_struct_3918_);
lean_inc_ref(v_post_3877_);
lean_inc_ref(v_pre_3875_);
v___x_3919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v_struct_3918_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; size_t v___x_3921_; size_t v___x_3922_; uint8_t v___x_3923_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref(v___x_3919_);
v___x_3921_ = lean_ptr_addr(v_struct_3918_);
v___x_3922_ = lean_ptr_addr(v_a_3920_);
v___x_3923_ = lean_usize_dec_eq(v___x_3921_, v___x_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_inc(v_idx_3917_);
lean_inc(v_typeName_3916_);
lean_dec_ref(v___y_3893_);
v___x_3924_ = l_Lean_Expr_proj___override(v_typeName_3916_, v_idx_3917_, v_a_3920_);
v___x_3925_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___x_3924_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; 
lean_dec(v_a_3920_);
v___x_3926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3926_;
}
}
else
{
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v_post_3877_);
lean_dec_ref(v_pre_3875_);
return v___x_3919_;
}
}
default: 
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3875_, v_post_3877_, v_usedLetOnly_3878_, v_skipConstInApp_3879_, v_skipInstances_3880_, v___y_3893_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3927_;
}
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v_post_3877_);
lean_dec_ref(v_e_3876_);
lean_dec_ref(v_pre_3875_);
v_a_3937_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3887_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3887_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_3945_, lean_object* v_e_3946_, lean_object* v_post_3947_, lean_object* v_usedLetOnly_3948_, lean_object* v_skipConstInApp_3949_, lean_object* v_skipInstances_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v_usedLetOnly_boxed_3957_; uint8_t v_skipConstInApp_boxed_3958_; uint8_t v_skipInstances_boxed_3959_; lean_object* v_res_3960_; 
v_usedLetOnly_boxed_3957_ = lean_unbox(v_usedLetOnly_3948_);
v_skipConstInApp_boxed_3958_ = lean_unbox(v_skipConstInApp_3949_);
v_skipInstances_boxed_3959_ = lean_unbox(v_skipInstances_3950_);
v_res_3960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v_pre_3945_, v_e_3946_, v_post_3947_, v_usedLetOnly_boxed_3957_, v_skipConstInApp_boxed_3958_, v_skipInstances_boxed_3959_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_3961_, lean_object* v_post_3962_, uint8_t v_usedLetOnly_3963_, uint8_t v_skipConstInApp_3964_, uint8_t v_skipInstances_3965_, lean_object* v_e_3966_, lean_object* v_a_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_inc(v_a_3967_);
v___x_3973_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3973_, 0, lean_box(0));
lean_closure_set(v___x_3973_, 1, lean_box(0));
lean_closure_set(v___x_3973_, 2, v_a_3967_);
v___x_3974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3973_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4008_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_4008_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4008_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_3975_, v_e_3966_);
lean_dec(v_a_3975_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___f_3983_; lean_object* v___x_3984_; 
lean_del_object(v___x_3977_);
v___x_3980_ = lean_box(v_usedLetOnly_3963_);
v___x_3981_ = lean_box(v_skipConstInApp_3964_);
v___x_3982_ = lean_box(v_skipInstances_3965_);
lean_inc_ref(v_e_3966_);
v___f_3983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3983_, 0, v_pre_3961_);
lean_closure_set(v___f_3983_, 1, v_e_3966_);
lean_closure_set(v___f_3983_, 2, v_post_3962_);
lean_closure_set(v___f_3983_, 3, v___x_3980_);
lean_closure_set(v___f_3983_, 4, v___x_3981_);
lean_closure_set(v___f_3983_, 5, v___x_3982_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v_a_3967_);
v___x_3984_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_3983_, v_a_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___f_3986_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref(v___x_3984_);
lean_inc(v_a_3985_);
v___f_3986_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3986_, 0, v_a_3967_);
lean_closure_set(v___f_3986_, 1, v_e_3966_);
lean_closure_set(v___f_3986_, 2, v_a_3985_);
v___x_3987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3986_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v___x_3987_, 0);
lean_dec(v_unused_3995_);
v___x_3989_ = v___x_3987_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v___x_3987_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_a_3985_);
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3985_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v_a_3985_);
v_a_3996_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3987_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3987_);
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
else
{
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_e_3966_);
return v___x_3984_;
}
}
else
{
lean_object* v_val_4004_; lean_object* v___x_4006_; 
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_e_3966_);
lean_dec_ref(v_post_3962_);
lean_dec_ref(v_pre_3961_);
v_val_4004_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_4004_);
lean_dec_ref(v___x_3979_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_val_4004_);
v___x_4006_ = v___x_3977_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_val_4004_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_e_3966_);
lean_dec_ref(v_post_3962_);
lean_dec_ref(v_pre_3961_);
v_a_4009_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3974_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3974_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4017_, lean_object* v_pre_4018_, lean_object* v_post_4019_, lean_object* v_usedLetOnly_4020_, lean_object* v_skipConstInApp_4021_, lean_object* v_skipInstances_4022_, lean_object* v_body_4023_, lean_object* v_x_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
uint8_t v_usedLetOnly_boxed_4031_; uint8_t v_skipConstInApp_boxed_4032_; uint8_t v_skipInstances_boxed_4033_; lean_object* v_res_4034_; 
v_usedLetOnly_boxed_4031_ = lean_unbox(v_usedLetOnly_4020_);
v_skipConstInApp_boxed_4032_ = lean_unbox(v_skipConstInApp_4021_);
v_skipInstances_boxed_4033_ = lean_unbox(v_skipInstances_4022_);
v_res_4034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4017_, v_pre_4018_, v_post_4019_, v_usedLetOnly_boxed_4031_, v_skipConstInApp_boxed_4032_, v_skipInstances_boxed_4033_, v_body_4023_, v_x_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4035_, lean_object* v_post_4036_, uint8_t v_usedLetOnly_4037_, uint8_t v_skipConstInApp_4038_, uint8_t v_skipInstances_4039_, lean_object* v_fvars_4040_, lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
if (lean_obj_tag(v_e_4041_) == 7)
{
lean_object* v_binderName_4048_; lean_object* v_binderType_4049_; lean_object* v_body_4050_; uint8_t v_binderInfo_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_binderName_4048_ = lean_ctor_get(v_e_4041_, 0);
lean_inc(v_binderName_4048_);
v_binderType_4049_ = lean_ctor_get(v_e_4041_, 1);
lean_inc_ref(v_binderType_4049_);
v_body_4050_ = lean_ctor_get(v_e_4041_, 2);
lean_inc_ref(v_body_4050_);
v_binderInfo_4051_ = lean_ctor_get_uint8(v_e_4041_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4041_);
v___x_4052_ = lean_expr_instantiate_rev(v_binderType_4049_, v_fvars_4040_);
lean_dec_ref(v_binderType_4049_);
lean_inc(v___y_4046_);
lean_inc_ref(v___y_4045_);
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
lean_inc(v_a_4042_);
lean_inc_ref(v_post_4036_);
lean_inc_ref(v_pre_4035_);
v___x_4053_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4035_, v_post_4036_, v_usedLetOnly_4037_, v_skipConstInApp_4038_, v_skipInstances_4039_, v___x_4052_, v_a_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___f_4058_; uint8_t v___x_4059_; lean_object* v___x_4060_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = lean_box(v_usedLetOnly_4037_);
v___x_4056_ = lean_box(v_skipConstInApp_4038_);
v___x_4057_ = lean_box(v_skipInstances_4039_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4058_, 0, v_fvars_4040_);
lean_closure_set(v___f_4058_, 1, v_pre_4035_);
lean_closure_set(v___f_4058_, 2, v_post_4036_);
lean_closure_set(v___f_4058_, 3, v___x_4055_);
lean_closure_set(v___f_4058_, 4, v___x_4056_);
lean_closure_set(v___f_4058_, 5, v___x_4057_);
lean_closure_set(v___f_4058_, 6, v_body_4050_);
v___x_4059_ = 0;
v___x_4060_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4048_, v_binderInfo_4051_, v_a_4054_, v___f_4058_, v___x_4059_, v_a_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4060_;
}
else
{
lean_dec_ref(v_body_4050_);
lean_dec(v_binderName_4048_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_fvars_4040_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
return v___x_4053_;
}
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_expr_instantiate_rev(v_e_4041_, v_fvars_4040_);
lean_dec_ref(v_e_4041_);
lean_inc(v___y_4046_);
lean_inc_ref(v___y_4045_);
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
lean_inc(v_a_4042_);
lean_inc_ref(v_post_4036_);
lean_inc_ref(v_pre_4035_);
v___x_4062_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4035_, v_post_4036_, v_usedLetOnly_4037_, v_skipConstInApp_4038_, v_skipInstances_4039_, v___x_4061_, v_a_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; uint8_t v___x_4064_; uint8_t v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = 0;
v___x_4065_ = 1;
v___x_4066_ = 1;
v___x_4067_ = l_Lean_Meta_mkForallFVars(v_fvars_4040_, v_a_4063_, v___x_4064_, v_usedLetOnly_4037_, v___x_4065_, v___x_4066_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec_ref(v_fvars_4040_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref(v___x_4067_);
v___x_4069_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4035_, v_post_4036_, v_usedLetOnly_4037_, v_skipConstInApp_4038_, v_skipInstances_4039_, v_a_4068_, v_a_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4069_;
}
else
{
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
return v___x_4067_;
}
}
else
{
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_fvars_4040_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
return v___x_4062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4070_, lean_object* v_pre_4071_, lean_object* v_post_4072_, uint8_t v_usedLetOnly_4073_, uint8_t v_skipConstInApp_4074_, uint8_t v_skipInstances_4075_, lean_object* v_body_4076_, lean_object* v_x_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_array_push(v_fvars_4070_, v_x_4077_);
v___x_4085_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4071_, v_post_4072_, v_usedLetOnly_4073_, v_skipConstInApp_4074_, v_skipInstances_4075_, v___x_4084_, v_body_4076_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4086_, lean_object* v_post_4087_, lean_object* v_usedLetOnly_4088_, lean_object* v_skipConstInApp_4089_, lean_object* v_skipInstances_4090_, lean_object* v_e_4091_, lean_object* v_a_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v_usedLetOnly_boxed_4098_; uint8_t v_skipConstInApp_boxed_4099_; uint8_t v_skipInstances_boxed_4100_; lean_object* v_res_4101_; 
v_usedLetOnly_boxed_4098_ = lean_unbox(v_usedLetOnly_4088_);
v_skipConstInApp_boxed_4099_ = lean_unbox(v_skipConstInApp_4089_);
v_skipInstances_boxed_4100_ = lean_unbox(v_skipInstances_4090_);
v_res_4101_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4086_, v_post_4087_, v_usedLetOnly_boxed_4098_, v_skipConstInApp_boxed_4099_, v_skipInstances_boxed_4100_, v_e_4091_, v_a_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4102_, lean_object* v_post_4103_, lean_object* v_usedLetOnly_4104_, lean_object* v_skipConstInApp_4105_, lean_object* v_skipInstances_4106_, lean_object* v_sz_4107_, lean_object* v_i_4108_, lean_object* v_bs_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v_usedLetOnly_boxed_4116_; uint8_t v_skipConstInApp_boxed_4117_; uint8_t v_skipInstances_boxed_4118_; size_t v_sz_boxed_4119_; size_t v_i_boxed_4120_; lean_object* v_res_4121_; 
v_usedLetOnly_boxed_4116_ = lean_unbox(v_usedLetOnly_4104_);
v_skipConstInApp_boxed_4117_ = lean_unbox(v_skipConstInApp_4105_);
v_skipInstances_boxed_4118_ = lean_unbox(v_skipInstances_4106_);
v_sz_boxed_4119_ = lean_unbox_usize(v_sz_4107_);
lean_dec(v_sz_4107_);
v_i_boxed_4120_ = lean_unbox_usize(v_i_4108_);
lean_dec(v_i_4108_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4102_, v_post_4103_, v_usedLetOnly_boxed_4116_, v_skipConstInApp_boxed_4117_, v_skipInstances_boxed_4118_, v_sz_boxed_4119_, v_i_boxed_4120_, v_bs_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4122_, lean_object* v_post_4123_, lean_object* v_usedLetOnly_4124_, lean_object* v_skipConstInApp_4125_, lean_object* v_skipInstances_4126_, lean_object* v_e_4127_, lean_object* v_a_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v_usedLetOnly_boxed_4134_; uint8_t v_skipConstInApp_boxed_4135_; uint8_t v_skipInstances_boxed_4136_; lean_object* v_res_4137_; 
v_usedLetOnly_boxed_4134_ = lean_unbox(v_usedLetOnly_4124_);
v_skipConstInApp_boxed_4135_ = lean_unbox(v_skipConstInApp_4125_);
v_skipInstances_boxed_4136_ = lean_unbox(v_skipInstances_4126_);
v_res_4137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4122_, v_post_4123_, v_usedLetOnly_boxed_4134_, v_skipConstInApp_boxed_4135_, v_skipInstances_boxed_4136_, v_e_4127_, v_a_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4138_, lean_object* v_post_4139_, lean_object* v_usedLetOnly_4140_, lean_object* v_skipConstInApp_4141_, lean_object* v_skipInstances_4142_, lean_object* v_fvars_4143_, lean_object* v_e_4144_, lean_object* v_a_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
uint8_t v_usedLetOnly_boxed_4151_; uint8_t v_skipConstInApp_boxed_4152_; uint8_t v_skipInstances_boxed_4153_; lean_object* v_res_4154_; 
v_usedLetOnly_boxed_4151_ = lean_unbox(v_usedLetOnly_4140_);
v_skipConstInApp_boxed_4152_ = lean_unbox(v_skipConstInApp_4141_);
v_skipInstances_boxed_4153_ = lean_unbox(v_skipInstances_4142_);
v_res_4154_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4138_, v_post_4139_, v_usedLetOnly_boxed_4151_, v_skipConstInApp_boxed_4152_, v_skipInstances_boxed_4153_, v_fvars_4143_, v_e_4144_, v_a_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4155_, lean_object* v_post_4156_, lean_object* v_usedLetOnly_4157_, lean_object* v_skipConstInApp_4158_, lean_object* v_skipInstances_4159_, lean_object* v_fvars_4160_, lean_object* v_e_4161_, lean_object* v_a_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v_usedLetOnly_boxed_4168_; uint8_t v_skipConstInApp_boxed_4169_; uint8_t v_skipInstances_boxed_4170_; lean_object* v_res_4171_; 
v_usedLetOnly_boxed_4168_ = lean_unbox(v_usedLetOnly_4157_);
v_skipConstInApp_boxed_4169_ = lean_unbox(v_skipConstInApp_4158_);
v_skipInstances_boxed_4170_ = lean_unbox(v_skipInstances_4159_);
v_res_4171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4155_, v_post_4156_, v_usedLetOnly_boxed_4168_, v_skipConstInApp_boxed_4169_, v_skipInstances_boxed_4170_, v_fvars_4160_, v_e_4161_, v_a_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4172_, lean_object* v_post_4173_, lean_object* v_usedLetOnly_4174_, lean_object* v_skipConstInApp_4175_, lean_object* v_skipInstances_4176_, lean_object* v_fvars_4177_, lean_object* v_e_4178_, lean_object* v_a_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v_usedLetOnly_boxed_4185_; uint8_t v_skipConstInApp_boxed_4186_; uint8_t v_skipInstances_boxed_4187_; lean_object* v_res_4188_; 
v_usedLetOnly_boxed_4185_ = lean_unbox(v_usedLetOnly_4174_);
v_skipConstInApp_boxed_4186_ = lean_unbox(v_skipConstInApp_4175_);
v_skipInstances_boxed_4187_ = lean_unbox(v_skipInstances_4176_);
v_res_4188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4172_, v_post_4173_, v_usedLetOnly_boxed_4185_, v_skipConstInApp_boxed_4186_, v_skipInstances_boxed_4187_, v_fvars_4177_, v_e_4178_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4189_, lean_object* v___x_4190_, lean_object* v_pre_4191_, lean_object* v_post_4192_, lean_object* v_usedLetOnly_4193_, lean_object* v_skipConstInApp_4194_, lean_object* v_skipInstances_4195_, lean_object* v_a_4196_, lean_object* v_b_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
uint8_t v_usedLetOnly_boxed_4204_; uint8_t v_skipConstInApp_boxed_4205_; uint8_t v_skipInstances_boxed_4206_; lean_object* v_res_4207_; 
v_usedLetOnly_boxed_4204_ = lean_unbox(v_usedLetOnly_4193_);
v_skipConstInApp_boxed_4205_ = lean_unbox(v_skipConstInApp_4194_);
v_skipInstances_boxed_4206_ = lean_unbox(v_skipInstances_4195_);
v_res_4207_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4189_, v___x_4190_, v_pre_4191_, v_post_4192_, v_usedLetOnly_boxed_4204_, v_skipConstInApp_boxed_4205_, v_skipInstances_boxed_4206_, v_a_4196_, v_b_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec_ref(v___x_4190_);
lean_dec(v_upperBound_4189_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4208_, lean_object* v_pre_4209_, lean_object* v_post_4210_, lean_object* v_usedLetOnly_4211_, lean_object* v_skipConstInApp_4212_, lean_object* v_x_4213_, lean_object* v_x_4214_, lean_object* v_x_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
uint8_t v_skipInstances_boxed_4222_; uint8_t v_usedLetOnly_boxed_4223_; uint8_t v_skipConstInApp_boxed_4224_; lean_object* v_res_4225_; 
v_skipInstances_boxed_4222_ = lean_unbox(v_skipInstances_4208_);
v_usedLetOnly_boxed_4223_ = lean_unbox(v_usedLetOnly_4211_);
v_skipConstInApp_boxed_4224_ = lean_unbox(v_skipConstInApp_4212_);
v_res_4225_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4222_, v_pre_4209_, v_post_4210_, v_usedLetOnly_boxed_4223_, v_skipConstInApp_boxed_4224_, v_x_4213_, v_x_4214_, v_x_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4226_, lean_object* v_pre_4227_, lean_object* v_post_4228_, uint8_t v_usedLetOnly_4229_, uint8_t v_skipConstInApp_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_a_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; 
v___x_4236_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4237_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4236_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref(v___x_4237_);
v___x_4239_ = 0;
lean_inc(v___y_4234_);
lean_inc_ref(v___y_4233_);
lean_inc(v___y_4232_);
lean_inc_ref(v___y_4231_);
lean_inc(v_a_4238_);
v___x_4240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4227_, v_post_4228_, v_usedLetOnly_4229_, v_skipConstInApp_4230_, v___x_4239_, v_input_4226_, v_a_4238_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v___x_4240_);
v___x_4242_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4242_, 0, lean_box(0));
lean_closure_set(v___x_4242_, 1, lean_box(0));
lean_closure_set(v___x_4242_, 2, v_a_4238_);
v___x_4243_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4242_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v___x_4243_, 0);
lean_dec(v_unused_4251_);
v___x_4245_ = v___x_4243_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_dec(v___x_4243_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v_a_4241_);
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4241_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_dec(v_a_4238_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4252_, lean_object* v_pre_4253_, lean_object* v_post_4254_, lean_object* v_usedLetOnly_4255_, lean_object* v_skipConstInApp_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
uint8_t v_usedLetOnly_boxed_4262_; uint8_t v_skipConstInApp_boxed_4263_; lean_object* v_res_4264_; 
v_usedLetOnly_boxed_4262_ = lean_unbox(v_usedLetOnly_4255_);
v_skipConstInApp_boxed_4263_ = lean_unbox(v_skipConstInApp_4256_);
v_res_4264_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4252_, v_pre_4253_, v_post_4254_, v_usedLetOnly_boxed_4262_, v_skipConstInApp_boxed_4263_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4266_, uint8_t v_zetaDelta_4267_, uint8_t v_zetaHave_4268_, uint8_t v_beta_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_lctx_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___f_4279_; uint8_t v___x_4280_; 
v_lctx_4275_ = lean_ctor_get(v_a_4270_, 2);
lean_inc_ref(v_lctx_4275_);
v___x_4276_ = lean_local_ctx_num_indices(v_lctx_4275_);
v___x_4277_ = lean_box(v_zetaHave_4268_);
v___x_4278_ = lean_box(v_zetaDelta_4267_);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4279_, 0, v___x_4277_);
lean_closure_set(v___f_4279_, 1, v___x_4276_);
lean_closure_set(v___f_4279_, 2, v___x_4278_);
v___x_4280_ = 1;
if (v_beta_4269_ == 0)
{
lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; 
v___f_4281_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4282_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4282_, 0, v___f_4279_);
v___x_4283_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4266_, v___f_4282_, v___f_4281_, v___x_4280_, v_beta_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
return v___x_4283_;
}
else
{
lean_object* v___f_4284_; lean_object* v___f_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; 
v___f_4284_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4285_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4285_, 0, v___f_4279_);
v___x_4286_ = 0;
v___x_4287_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4266_, v___f_4285_, v___f_4284_, v___x_4280_, v___x_4286_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
return v___x_4287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4288_, lean_object* v_zetaDelta_4289_, lean_object* v_zetaHave_4290_, lean_object* v_beta_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
uint8_t v_zetaDelta_boxed_4297_; uint8_t v_zetaHave_boxed_4298_; uint8_t v_beta_boxed_4299_; lean_object* v_res_4300_; 
v_zetaDelta_boxed_4297_ = lean_unbox(v_zetaDelta_4289_);
v_zetaHave_boxed_4298_ = lean_unbox(v_zetaHave_4290_);
v_beta_boxed_4299_ = lean_unbox(v_beta_4291_);
v_res_4300_ = l_Lean_Meta_zetaReduce(v_e_4288_, v_zetaDelta_boxed_4297_, v_zetaHave_boxed_4298_, v_beta_boxed_4299_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4301_, lean_object* v___x_4302_, lean_object* v_pre_4303_, lean_object* v_post_4304_, uint8_t v_usedLetOnly_4305_, uint8_t v_skipConstInApp_4306_, uint8_t v_skipInstances_4307_, lean_object* v___x_4308_, lean_object* v_inst_4309_, lean_object* v_R_4310_, lean_object* v_a_4311_, lean_object* v_b_4312_, lean_object* v_c_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4301_, v___x_4302_, v_pre_4303_, v_post_4304_, v_usedLetOnly_4305_, v_skipConstInApp_4306_, v_skipInstances_4307_, v_a_4311_, v_b_4312_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4321_ = _args[0];
lean_object* v___x_4322_ = _args[1];
lean_object* v_pre_4323_ = _args[2];
lean_object* v_post_4324_ = _args[3];
lean_object* v_usedLetOnly_4325_ = _args[4];
lean_object* v_skipConstInApp_4326_ = _args[5];
lean_object* v_skipInstances_4327_ = _args[6];
lean_object* v___x_4328_ = _args[7];
lean_object* v_inst_4329_ = _args[8];
lean_object* v_R_4330_ = _args[9];
lean_object* v_a_4331_ = _args[10];
lean_object* v_b_4332_ = _args[11];
lean_object* v_c_4333_ = _args[12];
lean_object* v___y_4334_ = _args[13];
lean_object* v___y_4335_ = _args[14];
lean_object* v___y_4336_ = _args[15];
lean_object* v___y_4337_ = _args[16];
lean_object* v___y_4338_ = _args[17];
lean_object* v___y_4339_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4340_; uint8_t v_skipConstInApp_boxed_4341_; uint8_t v_skipInstances_boxed_4342_; lean_object* v_res_4343_; 
v_usedLetOnly_boxed_4340_ = lean_unbox(v_usedLetOnly_4325_);
v_skipConstInApp_boxed_4341_ = lean_unbox(v_skipConstInApp_4326_);
v_skipInstances_boxed_4342_ = lean_unbox(v_skipInstances_4327_);
v_res_4343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4321_, v___x_4322_, v_pre_4323_, v_post_4324_, v_usedLetOnly_boxed_4340_, v_skipConstInApp_boxed_4341_, v_skipInstances_boxed_4342_, v___x_4328_, v_inst_4329_, v_R_4330_, v_a_4331_, v_b_4332_, v_c_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___x_4328_);
lean_dec_ref(v___x_4322_);
lean_dec(v_upperBound_4321_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4344_, lean_object* v_name_4345_, uint8_t v_bi_4346_, lean_object* v_type_4347_, lean_object* v_k_4348_, uint8_t v_kind_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4345_, v_bi_4346_, v_type_4347_, v_k_4348_, v_kind_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4357_, lean_object* v_name_4358_, lean_object* v_bi_4359_, lean_object* v_type_4360_, lean_object* v_k_4361_, lean_object* v_kind_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
uint8_t v_bi_boxed_4369_; uint8_t v_kind_boxed_4370_; lean_object* v_res_4371_; 
v_bi_boxed_4369_ = lean_unbox(v_bi_4359_);
v_kind_boxed_4370_ = lean_unbox(v_kind_4362_);
v_res_4371_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4357_, v_name_4358_, v_bi_boxed_4369_, v_type_4360_, v_k_4361_, v_kind_boxed_4370_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4372_, lean_object* v_name_4373_, lean_object* v_type_4374_, lean_object* v_val_4375_, lean_object* v_k_4376_, uint8_t v_nondep_4377_, uint8_t v_kind_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4373_, v_type_4374_, v_val_4375_, v_k_4376_, v_nondep_4377_, v_kind_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_name_4387_, lean_object* v_type_4388_, lean_object* v_val_4389_, lean_object* v_k_4390_, lean_object* v_nondep_4391_, lean_object* v_kind_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v_nondep_boxed_4399_; uint8_t v_kind_boxed_4400_; lean_object* v_res_4401_; 
v_nondep_boxed_4399_ = lean_unbox(v_nondep_4391_);
v_kind_boxed_4400_ = lean_unbox(v_kind_4392_);
v_res_4401_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4386_, v_name_4387_, v_type_4388_, v_val_4389_, v_k_4390_, v_nondep_boxed_4399_, v_kind_boxed_4400_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4402_, lean_object* v_ref_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4403_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4410_, lean_object* v_ref_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4410_, v_ref_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4418_, lean_object* v_x_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_x_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4427_, v_x_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v_res_4435_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4436_, lean_object* v_as_4437_, size_t v_i_4438_, size_t v_stop_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_eq(v_i_4438_, v_stop_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4441_ = lean_array_uget_borrowed(v_as_4437_, v_i_4438_);
v___x_4442_ = l_Lean_instBEqFVarId_beq(v_a_4436_, v___x_4441_);
if (v___x_4442_ == 0)
{
size_t v___x_4443_; size_t v___x_4444_; 
v___x_4443_ = ((size_t)1ULL);
v___x_4444_ = lean_usize_add(v_i_4438_, v___x_4443_);
v_i_4438_ = v___x_4444_;
goto _start;
}
else
{
return v___x_4442_;
}
}
else
{
uint8_t v___x_4446_; 
v___x_4446_ = 0;
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4447_, lean_object* v_as_4448_, lean_object* v_i_4449_, lean_object* v_stop_4450_){
_start:
{
size_t v_i_boxed_4451_; size_t v_stop_boxed_4452_; uint8_t v_res_4453_; lean_object* v_r_4454_; 
v_i_boxed_4451_ = lean_unbox_usize(v_i_4449_);
lean_dec(v_i_4449_);
v_stop_boxed_4452_ = lean_unbox_usize(v_stop_4450_);
lean_dec(v_stop_4450_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4447_, v_as_4448_, v_i_boxed_4451_, v_stop_boxed_4452_);
lean_dec_ref(v_as_4448_);
lean_dec(v_a_4447_);
v_r_4454_ = lean_box(v_res_4453_);
return v_r_4454_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4457_ = lean_unsigned_to_nat(0u);
v___x_4458_ = lean_array_get_size(v_as_4455_);
v___x_4459_ = lean_nat_dec_lt(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
return v___x_4459_;
}
else
{
if (v___x_4459_ == 0)
{
return v___x_4459_;
}
else
{
size_t v___x_4460_; size_t v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = ((size_t)0ULL);
v___x_4461_ = lean_usize_of_nat(v___x_4458_);
v___x_4462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4456_, v_as_4455_, v___x_4460_, v___x_4461_);
return v___x_4462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4463_, lean_object* v_a_4464_){
_start:
{
uint8_t v_res_4465_; lean_object* v_r_4466_; 
v_res_4465_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_as_4463_);
v_r_4466_ = lean_box(v_res_4465_);
return v_r_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4467_, lean_object* v_e_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Lean_Expr_getAppFn(v_e_4468_);
if (lean_obj_tag(v___x_4477_) == 1)
{
lean_object* v_fvarId_4478_; uint8_t v___x_4479_; 
v_fvarId_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_fvarId_4478_);
lean_dec_ref(v___x_4477_);
v___x_4479_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4467_, v_fvarId_4478_);
if (v___x_4479_ == 0)
{
lean_dec(v_fvarId_4478_);
lean_dec_ref(v___y_4469_);
lean_dec_ref(v_e_4468_);
goto v___jp_4474_;
}
else
{
uint8_t v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = 0;
v___x_4481_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4478_, v___x_4480_, v___y_4469_, v___y_4471_, v___y_4472_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref(v___x_4481_);
if (lean_obj_tag(v_a_4482_) == 1)
{
lean_object* v_val_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4506_; 
v_val_4483_ = lean_ctor_get(v_a_4482_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4485_ = v_a_4482_;
v_isShared_4486_ = v_isSharedCheck_4506_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_val_4483_);
lean_dec(v_a_4482_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4506_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4505_; 
v___x_4487_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4483_, v___y_4470_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4505_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4505_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_dummy_4492_; lean_object* v_nargs_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v_dummy_4492_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4493_ = l_Lean_Expr_getAppNumArgs(v_e_4468_);
lean_inc(v_nargs_4493_);
v___x_4494_ = lean_mk_array(v_nargs_4493_, v_dummy_4492_);
v___x_4495_ = lean_unsigned_to_nat(1u);
v___x_4496_ = lean_nat_sub(v_nargs_4493_, v___x_4495_);
lean_dec(v_nargs_4493_);
v___x_4497_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4468_, v___x_4494_, v___x_4496_);
v___x_4498_ = l_Lean_Expr_beta(v_a_4488_, v___x_4497_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 0, v___x_4498_);
v___x_4500_ = v___x_4485_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4500_);
v___x_4502_ = v___x_4490_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
else
{
lean_dec(v_a_4482_);
lean_dec_ref(v_e_4468_);
goto v___jp_4474_;
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec_ref(v_e_4468_);
v_a_4507_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4481_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4481_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
lean_dec_ref(v___x_4477_);
lean_dec_ref(v___y_4469_);
lean_dec_ref(v_e_4468_);
v___x_4515_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
v___jp_4474_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4517_, lean_object* v_e_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4517_, v_e_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v_fvars_4517_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4525_, lean_object* v_fvars_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v___f_4532_; lean_object* v_pre_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; 
v___f_4532_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4533_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4533_, 0, v_fvars_4526_);
v___x_4534_ = 0;
v___x_4535_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4525_, v_pre_4533_, v___f_4532_, v___x_4534_, v___x_4534_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4536_, lean_object* v_fvars_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Meta_zetaDeltaFVars(v_e_4536_, v_fvars_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
return v_res_4543_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4544_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; lean_object* v_nextMacroScope_4553_; lean_object* v_ngen_4554_; lean_object* v_auxDeclNGen_4555_; lean_object* v_traceState_4556_; lean_object* v_messages_4557_; lean_object* v_infoState_4558_; lean_object* v_snapshotTasks_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4570_; 
v___x_4552_ = lean_st_ref_take(v___y_4550_);
v_nextMacroScope_4553_ = lean_ctor_get(v___x_4552_, 1);
v_ngen_4554_ = lean_ctor_get(v___x_4552_, 2);
v_auxDeclNGen_4555_ = lean_ctor_get(v___x_4552_, 3);
v_traceState_4556_ = lean_ctor_get(v___x_4552_, 4);
v_messages_4557_ = lean_ctor_get(v___x_4552_, 6);
v_infoState_4558_ = lean_ctor_get(v___x_4552_, 7);
v_snapshotTasks_4559_ = lean_ctor_get(v___x_4552_, 8);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; lean_object* v_unused_4572_; 
v_unused_4571_ = lean_ctor_get(v___x_4552_, 5);
lean_dec(v_unused_4571_);
v_unused_4572_ = lean_ctor_get(v___x_4552_, 0);
lean_dec(v_unused_4572_);
v___x_4561_ = v___x_4552_;
v_isShared_4562_ = v_isSharedCheck_4570_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_snapshotTasks_4559_);
lean_inc(v_infoState_4558_);
lean_inc(v_messages_4557_);
lean_inc(v_traceState_4556_);
lean_inc(v_auxDeclNGen_4555_);
lean_inc(v_ngen_4554_);
lean_inc(v_nextMacroScope_4553_);
lean_dec(v___x_4552_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4570_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; lean_object* v___x_4565_; 
v___x_4563_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 5, v___x_4563_);
lean_ctor_set(v___x_4561_, 0, v_env_4549_);
v___x_4565_ = v___x_4561_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_env_4549_);
lean_ctor_set(v_reuseFailAlloc_4569_, 1, v_nextMacroScope_4553_);
lean_ctor_set(v_reuseFailAlloc_4569_, 2, v_ngen_4554_);
lean_ctor_set(v_reuseFailAlloc_4569_, 3, v_auxDeclNGen_4555_);
lean_ctor_set(v_reuseFailAlloc_4569_, 4, v_traceState_4556_);
lean_ctor_set(v_reuseFailAlloc_4569_, 5, v___x_4563_);
lean_ctor_set(v_reuseFailAlloc_4569_, 6, v_messages_4557_);
lean_ctor_set(v_reuseFailAlloc_4569_, 7, v_infoState_4558_);
lean_ctor_set(v_reuseFailAlloc_4569_, 8, v_snapshotTasks_4559_);
v___x_4565_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4566_ = lean_st_ref_set(v___y_4550_, v___x_4565_);
v___x_4567_ = lean_box(0);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4573_, v___y_4574_);
lean_dec(v___y_4574_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4577_, v___y_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4587_, lean_object* v___x_4588_, uint8_t v___x_4589_, lean_object* v_e_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
if (lean_obj_tag(v_e_4590_) == 4)
{
lean_object* v_declName_4594_; lean_object* v_us_4595_; uint8_t v___x_4596_; uint8_t v___x_4597_; 
v_declName_4594_ = lean_ctor_get(v_e_4590_, 0);
v_us_4595_ = lean_ctor_get(v_e_4590_, 1);
v___x_4596_ = 1;
lean_inc(v_declName_4594_);
v___x_4597_ = l_Lean_Environment_contains(v_env_4587_, v_declName_4594_, v___x_4596_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
lean_inc(v_declName_4594_);
v___x_4598_ = l_Lean_Environment_find_x3f(v___x_4588_, v_declName_4594_, v___x_4589_);
if (lean_obj_tag(v___x_4598_) == 1)
{
lean_object* v_val_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4628_; 
v_val_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4628_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_val_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4628_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
uint8_t v___x_4603_; 
v___x_4603_ = l_Lean_ConstantInfo_hasValue(v_val_4599_, v___x_4589_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4605_; 
lean_dec(v_val_4599_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set_tag(v___x_4601_, 0);
lean_ctor_set(v___x_4601_, 0, v_e_4590_);
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_e_4590_);
v___x_4605_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
}
else
{
lean_object* v___x_4608_; 
lean_inc(v_us_4595_);
lean_dec_ref(v_e_4590_);
v___x_4608_ = l_Lean_Core_instantiateValueLevelParams(v_val_4599_, v_us_4595_, v___y_4591_, v___y_4592_);
lean_dec(v_val_4599_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4619_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4611_ = v___x_4608_;
v_isShared_4612_ = v_isSharedCheck_4619_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4619_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v_a_4609_);
v___x_4614_ = v___x_4601_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4616_; 
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4614_);
v___x_4616_ = v___x_4611_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_del_object(v___x_4601_);
v_a_4620_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4608_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4608_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
lean_dec(v___x_4598_);
v___x_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4629_, 0, v_e_4590_);
v___x_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
return v___x_4630_;
}
}
else
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
lean_dec_ref(v___x_4588_);
v___x_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4631_, 0, v_e_4590_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
return v___x_4632_;
}
}
else
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec_ref(v_e_4590_);
lean_dec_ref(v___x_4588_);
lean_dec_ref(v_env_4587_);
v___x_4633_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4635_, lean_object* v___x_4636_, lean_object* v___x_4637_, lean_object* v_e_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
uint8_t v___x_2938__boxed_4642_; lean_object* v_res_4643_; 
v___x_2938__boxed_4642_ = lean_unbox(v___x_4637_);
v_res_4643_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4635_, v___x_4636_, v___x_2938__boxed_4642_, v_e_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4644_, lean_object* v_e_4645_, lean_object* v___f_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v___x_4650_; uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v_env_4654_; lean_object* v___x_4655_; lean_object* v___f_4656_; lean_object* v___x_4657_; 
v___x_4650_ = lean_st_ref_get(v___y_4648_);
v___x_4651_ = 0;
v___x_4652_ = l_Lean_Environment_setExporting(v_biggerEnv_4644_, v___x_4651_);
lean_inc_ref(v___x_4652_);
v___x_4653_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4652_, v___y_4648_);
lean_dec_ref(v___x_4653_);
v_env_4654_ = lean_ctor_get(v___x_4650_, 0);
lean_inc_ref(v_env_4654_);
lean_dec(v___x_4650_);
v___x_4655_ = lean_box(v___x_4651_);
v___f_4656_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4656_, 0, v_env_4654_);
lean_closure_set(v___f_4656_, 1, v___x_4652_);
lean_closure_set(v___f_4656_, 2, v___x_4655_);
v___x_4657_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4645_, v___f_4656_, v___f_4646_, v___y_4647_, v___y_4648_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4658_, lean_object* v_e_4659_, lean_object* v___f_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4658_, v_e_4659_, v___f_4660_, v___y_4661_, v___y_4662_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4665_, lean_object* v_x_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; lean_object* v_env_4671_; lean_object* v_a_4673_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4670_ = lean_st_ref_get(v___y_4668_);
v_env_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc_ref(v_env_4671_);
lean_dec(v___x_4670_);
v___x_4683_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4665_, v___y_4668_);
lean_dec_ref(v___x_4683_);
lean_inc(v___y_4668_);
v___x_4684_ = lean_apply_3(v_x_4666_, v___y_4667_, v___y_4668_, lean_box(0));
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref(v___x_4684_);
v___x_4686_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4671_, v___y_4668_);
lean_dec(v___y_4668_);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v___x_4686_, 0);
lean_dec(v_unused_4694_);
v___x_4688_ = v___x_4686_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_dec(v___x_4686_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v_a_4685_);
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4685_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
else
{
lean_object* v_a_4695_; 
v_a_4695_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4695_);
lean_dec_ref(v___x_4684_);
v_a_4673_ = v_a_4695_;
goto v___jp_4672_;
}
v___jp_4672_:
{
lean_object* v___x_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
v___x_4674_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4671_, v___y_4668_);
lean_dec(v___y_4668_);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; 
v_unused_4682_ = lean_ctor_get(v___x_4674_, 0);
lean_dec(v_unused_4682_);
v___x_4676_ = v___x_4674_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_dec(v___x_4674_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
lean_ctor_set_tag(v___x_4676_, 1);
lean_ctor_set(v___x_4676_, 0, v_a_4673_);
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4673_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4696_, lean_object* v_x_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4696_, v_x_4697_, v___y_4698_, v___y_4699_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_4702_, lean_object* v_e_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v___x_4707_; lean_object* v_env_4708_; lean_object* v___f_4709_; lean_object* v___f_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4707_ = lean_st_ref_get(v_a_4705_);
v_env_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc_ref(v_env_4708_);
lean_dec(v___x_4707_);
v___f_4709_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_4710_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_4710_, 0, v_biggerEnv_4702_);
lean_closure_set(v___f_4710_, 1, v_e_4703_);
lean_closure_set(v___f_4710_, 2, v___f_4709_);
v___x_4711_ = l_Lean_Environment_unlockAsync(v_env_4708_);
v___x_4712_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_4711_, v___f_4710_, v_a_4704_, v_a_4705_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_4713_, lean_object* v_e_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_4713_, v_e_4714_, v_a_4715_, v_a_4716_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_4719_, lean_object* v_env_4720_, lean_object* v_x_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4720_, v_x_4721_, v___y_4722_, v___y_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_4726_, lean_object* v_env_4727_, lean_object* v_x_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_4726_, v_env_4727_, v_x_4728_, v___y_4729_, v___y_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_4733_, lean_object* v_axs_4734_, lean_object* v_numSectionVars_4735_, lean_object* v_as_4736_, size_t v_i_4737_, size_t v_stop_4738_){
_start:
{
uint8_t v___x_4739_; 
v___x_4739_ = lean_usize_dec_eq(v_i_4737_, v_stop_4738_);
if (v___x_4739_ == 0)
{
uint8_t v___x_4740_; uint8_t v___y_4742_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4740_ = 1;
v___x_4746_ = lean_array_uget_borrowed(v_as_4736_, v_i_4737_);
v___x_4747_ = l_Lean_Expr_constName_x21(v_af_4733_);
v___x_4748_ = lean_name_eq(v___x_4747_, v___x_4746_);
lean_dec(v___x_4747_);
if (v___x_4748_ == 0)
{
v___y_4742_ = v___x_4748_;
goto v___jp_4741_;
}
else
{
lean_object* v___x_4749_; uint8_t v___x_4750_; 
v___x_4749_ = lean_array_get_size(v_axs_4734_);
v___x_4750_ = lean_nat_dec_le(v___x_4749_, v_numSectionVars_4735_);
v___y_4742_ = v___x_4750_;
goto v___jp_4741_;
}
v___jp_4741_:
{
if (v___y_4742_ == 0)
{
size_t v___x_4743_; size_t v___x_4744_; 
v___x_4743_ = ((size_t)1ULL);
v___x_4744_ = lean_usize_add(v_i_4737_, v___x_4743_);
v_i_4737_ = v___x_4744_;
goto _start;
}
else
{
return v___x_4740_;
}
}
}
else
{
uint8_t v___x_4751_; 
v___x_4751_ = 0;
return v___x_4751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_4752_, lean_object* v_axs_4753_, lean_object* v_numSectionVars_4754_, lean_object* v_as_4755_, lean_object* v_i_4756_, lean_object* v_stop_4757_){
_start:
{
size_t v_i_boxed_4758_; size_t v_stop_boxed_4759_; uint8_t v_res_4760_; lean_object* v_r_4761_; 
v_i_boxed_4758_ = lean_unbox_usize(v_i_4756_);
lean_dec(v_i_4756_);
v_stop_boxed_4759_ = lean_unbox_usize(v_stop_4757_);
lean_dec(v_stop_4757_);
v_res_4760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_4752_, v_axs_4753_, v_numSectionVars_4754_, v_as_4755_, v_i_boxed_4758_, v_stop_boxed_4759_);
lean_dec_ref(v_as_4755_);
lean_dec(v_numSectionVars_4754_);
lean_dec_ref(v_axs_4753_);
lean_dec_ref(v_af_4752_);
v_r_4761_ = lean_box(v_res_4760_);
return v_r_4761_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_4762_, lean_object* v_numSectionVars_4763_, lean_object* v_x_4764_, lean_object* v_x_4765_, lean_object* v_x_4766_){
_start:
{
if (lean_obj_tag(v_x_4764_) == 5)
{
lean_object* v_fn_4767_; lean_object* v_arg_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_fn_4767_ = lean_ctor_get(v_x_4764_, 0);
lean_inc_ref(v_fn_4767_);
v_arg_4768_ = lean_ctor_get(v_x_4764_, 1);
lean_inc_ref(v_arg_4768_);
lean_dec_ref(v_x_4764_);
v___x_4769_ = lean_array_set(v_x_4765_, v_x_4766_, v_arg_4768_);
v___x_4770_ = lean_unsigned_to_nat(1u);
v___x_4771_ = lean_nat_sub(v_x_4766_, v___x_4770_);
lean_dec(v_x_4766_);
v_x_4764_ = v_fn_4767_;
v_x_4765_ = v___x_4769_;
v_x_4766_ = v___x_4771_;
goto _start;
}
else
{
uint8_t v___x_4773_; 
lean_dec(v_x_4766_);
v___x_4773_ = l_Lean_Expr_isConst(v_x_4764_);
if (v___x_4773_ == 0)
{
lean_dec_ref(v_x_4765_);
lean_dec_ref(v_x_4764_);
return v___x_4773_;
}
else
{
lean_object* v___x_4774_; lean_object* v___x_4775_; uint8_t v___x_4776_; 
v___x_4774_ = lean_unsigned_to_nat(0u);
v___x_4775_ = lean_array_get_size(v_fnNames_4762_);
v___x_4776_ = lean_nat_dec_lt(v___x_4774_, v___x_4775_);
if (v___x_4776_ == 0)
{
lean_dec_ref(v_x_4765_);
lean_dec_ref(v_x_4764_);
return v___x_4776_;
}
else
{
if (v___x_4776_ == 0)
{
lean_dec_ref(v_x_4765_);
lean_dec_ref(v_x_4764_);
return v___x_4776_;
}
else
{
size_t v___x_4777_; size_t v___x_4778_; uint8_t v___x_4779_; 
v___x_4777_ = ((size_t)0ULL);
v___x_4778_ = lean_usize_of_nat(v___x_4775_);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_4764_, v_x_4765_, v_numSectionVars_4763_, v_fnNames_4762_, v___x_4777_, v___x_4778_);
lean_dec_ref(v_x_4765_);
lean_dec_ref(v_x_4764_);
return v___x_4779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_4780_, lean_object* v_numSectionVars_4781_, lean_object* v_x_4782_, lean_object* v_x_4783_, lean_object* v_x_4784_){
_start:
{
uint8_t v_res_4785_; lean_object* v_r_4786_; 
v_res_4785_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_4780_, v_numSectionVars_4781_, v_x_4782_, v_x_4783_, v_x_4784_);
lean_dec(v_numSectionVars_4781_);
lean_dec_ref(v_fnNames_4780_);
v_r_4786_ = lean_box(v_res_4785_);
return v_r_4786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_4787_, lean_object* v_fnNames_4788_, lean_object* v_x_4789_, lean_object* v_x_4790_, lean_object* v_x_4791_){
_start:
{
if (lean_obj_tag(v_x_4789_) == 5)
{
lean_object* v_fn_4792_; lean_object* v_arg_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; uint8_t v___x_4797_; 
v_fn_4792_ = lean_ctor_get(v_x_4789_, 0);
lean_inc_ref(v_fn_4792_);
v_arg_4793_ = lean_ctor_get(v_x_4789_, 1);
lean_inc_ref(v_arg_4793_);
lean_dec_ref(v_x_4789_);
v___x_4794_ = lean_array_set(v_x_4790_, v_x_4791_, v_arg_4793_);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = lean_nat_sub(v_x_4791_, v___x_4795_);
v___x_4797_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_4788_, v_numSectionVars_4787_, v_fn_4792_, v___x_4794_, v___x_4796_);
return v___x_4797_;
}
else
{
uint8_t v___x_4798_; 
v___x_4798_ = l_Lean_Expr_isConst(v_x_4789_);
if (v___x_4798_ == 0)
{
lean_dec_ref(v_x_4790_);
lean_dec_ref(v_x_4789_);
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; uint8_t v___x_4801_; 
v___x_4799_ = lean_unsigned_to_nat(0u);
v___x_4800_ = lean_array_get_size(v_fnNames_4788_);
v___x_4801_ = lean_nat_dec_lt(v___x_4799_, v___x_4800_);
if (v___x_4801_ == 0)
{
lean_dec_ref(v_x_4790_);
lean_dec_ref(v_x_4789_);
return v___x_4801_;
}
else
{
if (v___x_4801_ == 0)
{
lean_dec_ref(v_x_4790_);
lean_dec_ref(v_x_4789_);
return v___x_4801_;
}
else
{
size_t v___x_4802_; size_t v___x_4803_; uint8_t v___x_4804_; 
v___x_4802_ = ((size_t)0ULL);
v___x_4803_ = lean_usize_of_nat(v___x_4800_);
v___x_4804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_4789_, v_x_4790_, v_numSectionVars_4787_, v_fnNames_4788_, v___x_4802_, v___x_4803_);
lean_dec_ref(v_x_4790_);
lean_dec_ref(v_x_4789_);
return v___x_4804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_4805_, lean_object* v_fnNames_4806_, lean_object* v_x_4807_, lean_object* v_x_4808_, lean_object* v_x_4809_){
_start:
{
uint8_t v_res_4810_; lean_object* v_r_4811_; 
v_res_4810_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_4805_, v_fnNames_4806_, v_x_4807_, v_x_4808_, v_x_4809_);
lean_dec(v_x_4809_);
lean_dec_ref(v_fnNames_4806_);
lean_dec(v_numSectionVars_4805_);
v_r_4811_ = lean_box(v_res_4810_);
return v_r_4811_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_4812_, lean_object* v_numSectionVars_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v_dummy_4815_; lean_object* v_nargs_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; 
v_dummy_4815_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4816_ = l_Lean_Expr_getAppNumArgs(v_a_4814_);
lean_inc(v_nargs_4816_);
v___x_4817_ = lean_mk_array(v_nargs_4816_, v_dummy_4815_);
v___x_4818_ = lean_unsigned_to_nat(1u);
v___x_4819_ = lean_nat_sub(v_nargs_4816_, v___x_4818_);
lean_dec(v_nargs_4816_);
v___x_4820_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_4813_, v_fnNames_4812_, v_a_4814_, v___x_4817_, v___x_4819_);
lean_dec(v___x_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_4821_, lean_object* v_numSectionVars_4822_, lean_object* v_a_4823_){
_start:
{
uint8_t v_res_4824_; lean_object* v_r_4825_; 
v_res_4824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_4821_, v_numSectionVars_4822_, v_a_4823_);
lean_dec(v_numSectionVars_4822_);
lean_dec_ref(v_fnNames_4821_);
v_r_4825_ = lean_box(v_res_4824_);
return v_r_4825_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_4826_, lean_object* v_numSectionVars_4827_, lean_object* v_as_4828_, size_t v_i_4829_, size_t v_stop_4830_){
_start:
{
uint8_t v___x_4831_; 
v___x_4831_ = lean_usize_dec_eq(v_i_4829_, v_stop_4830_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4832_ = lean_array_uget_borrowed(v_as_4828_, v_i_4829_);
lean_inc(v___x_4832_);
v___x_4833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_4826_, v_numSectionVars_4827_, v___x_4832_);
if (v___x_4833_ == 0)
{
size_t v___x_4834_; size_t v___x_4835_; 
v___x_4834_ = ((size_t)1ULL);
v___x_4835_ = lean_usize_add(v_i_4829_, v___x_4834_);
v_i_4829_ = v___x_4835_;
goto _start;
}
else
{
return v___x_4833_;
}
}
else
{
uint8_t v___x_4837_; 
v___x_4837_ = 0;
return v___x_4837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_4838_, lean_object* v_numSectionVars_4839_, lean_object* v_as_4840_, lean_object* v_i_4841_, lean_object* v_stop_4842_){
_start:
{
size_t v_i_boxed_4843_; size_t v_stop_boxed_4844_; uint8_t v_res_4845_; lean_object* v_r_4846_; 
v_i_boxed_4843_ = lean_unbox_usize(v_i_4841_);
lean_dec(v_i_4841_);
v_stop_boxed_4844_ = lean_unbox_usize(v_stop_4842_);
lean_dec(v_stop_4842_);
v_res_4845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_4838_, v_numSectionVars_4839_, v_as_4840_, v_i_boxed_4843_, v_stop_boxed_4844_);
lean_dec_ref(v_as_4840_);
lean_dec(v_numSectionVars_4839_);
lean_dec_ref(v_fnNames_4838_);
v_r_4846_ = lean_box(v_res_4845_);
return v_r_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_4847_, lean_object* v_numSectionVars_4848_, lean_object* v___x_4849_, lean_object* v_x_4850_, lean_object* v_x_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
if (lean_obj_tag(v_x_4850_) == 5)
{
lean_object* v_fn_4858_; lean_object* v_arg_4859_; lean_object* v___x_4860_; 
v_fn_4858_ = lean_ctor_get(v_x_4850_, 0);
lean_inc_ref(v_fn_4858_);
v_arg_4859_ = lean_ctor_get(v_x_4850_, 1);
lean_inc_ref(v_arg_4859_);
lean_dec_ref(v_x_4850_);
v___x_4860_ = lean_array_push(v_x_4851_, v_arg_4859_);
v_x_4850_ = v_fn_4858_;
v_x_4851_ = v___x_4860_;
goto _start;
}
else
{
uint8_t v___x_4862_; 
v___x_4862_ = l_Lean_Expr_isConst(v_x_4850_);
if (v___x_4862_ == 0)
{
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
lean_dec_ref(v___x_4849_);
goto v___jp_4855_;
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = lean_array_get_size(v_x_4851_);
v___x_4865_ = lean_nat_dec_lt(v___x_4863_, v___x_4864_);
if (v___x_4865_ == 0)
{
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
lean_dec_ref(v___x_4849_);
goto v___jp_4855_;
}
else
{
if (v___x_4865_ == 0)
{
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
lean_dec_ref(v___x_4849_);
goto v___jp_4855_;
}
else
{
size_t v___x_4866_; size_t v___x_4867_; uint8_t v___x_4868_; 
v___x_4866_ = ((size_t)0ULL);
v___x_4867_ = lean_usize_of_nat(v___x_4864_);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_4847_, v_numSectionVars_4848_, v_x_4851_, v___x_4866_, v___x_4867_);
if (v___x_4868_ == 0)
{
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
lean_dec_ref(v___x_4849_);
goto v___jp_4855_;
}
else
{
lean_object* v___x_4869_; uint8_t v___x_4870_; lean_object* v___x_4871_; 
v___x_4869_ = l_Lean_Expr_constName_x21(v_x_4850_);
v___x_4870_ = 0;
v___x_4871_ = l_Lean_Environment_find_x3f(v___x_4849_, v___x_4869_, v___x_4870_);
if (lean_obj_tag(v___x_4871_) == 1)
{
lean_object* v_val_4872_; 
v_val_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_val_4872_);
lean_dec_ref(v___x_4871_);
if (lean_obj_tag(v_val_4872_) == 2)
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4898_; 
v___x_4873_ = l_Lean_Expr_constLevels_x21(v_x_4850_);
lean_dec_ref(v_x_4850_);
v___x_4874_ = l_Lean_Core_instantiateValueLevelParams(v_val_4872_, v___x_4873_, v___y_4852_, v___y_4853_);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_val_4872_);
if (v_isSharedCheck_4898_ == 0)
{
lean_object* v_unused_4899_; 
v_unused_4899_ = lean_ctor_get(v_val_4872_, 0);
lean_dec(v_unused_4899_);
v___x_4876_ = v_val_4872_;
v_isShared_4877_ = v_isSharedCheck_4898_;
goto v_resetjp_4875_;
}
else
{
lean_dec(v_val_4872_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4898_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4889_; 
v_a_4878_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4880_ = v___x_4874_;
v_isShared_4881_ = v_isSharedCheck_4889_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4874_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4889_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4882_ = l_Lean_Expr_betaRev(v_a_4878_, v_x_4851_, v___x_4870_, v___x_4870_);
lean_dec_ref(v_x_4851_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 1);
lean_ctor_set(v___x_4876_, 0, v___x_4882_);
v___x_4884_ = v___x_4876_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4886_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4884_);
v___x_4886_ = v___x_4880_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
else
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4897_; 
lean_del_object(v___x_4876_);
lean_dec_ref(v_x_4851_);
v_a_4890_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4892_ = v___x_4874_;
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4874_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
}
else
{
lean_dec(v_val_4872_);
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
goto v___jp_4855_;
}
}
else
{
lean_dec(v___x_4871_);
lean_dec_ref(v_x_4851_);
lean_dec_ref(v_x_4850_);
goto v___jp_4855_;
}
}
}
}
}
}
v___jp_4855_:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4856_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
return v___x_4857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_4900_, lean_object* v_numSectionVars_4901_, lean_object* v___x_4902_, lean_object* v_x_4903_, lean_object* v_x_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_4900_, v_numSectionVars_4901_, v___x_4902_, v_x_4903_, v_x_4904_, v___y_4905_, v___y_4906_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec(v_numSectionVars_4901_);
lean_dec_ref(v_fnNames_4900_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_4909_, lean_object* v_numSectionVars_4910_, lean_object* v_env_4911_, lean_object* v_e_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = l_Lean_Expr_getAppNumArgs(v_e_4912_);
v___x_4917_ = lean_mk_empty_array_with_capacity(v___x_4916_);
lean_dec(v___x_4916_);
v___x_4918_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_4909_, v_numSectionVars_4910_, v_env_4911_, v_e_4912_, v___x_4917_, v___y_4913_, v___y_4914_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_4919_, lean_object* v_numSectionVars_4920_, lean_object* v_env_4921_, lean_object* v_e_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_4919_, v_numSectionVars_4920_, v_env_4921_, v_e_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v_numSectionVars_4920_);
lean_dec_ref(v_fnNames_4919_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_4927_, lean_object* v_numSectionVars_4928_, lean_object* v_e_4929_, lean_object* v___f_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v___x_4934_; lean_object* v_env_4935_; lean_object* v___f_4936_; lean_object* v___x_4937_; 
v___x_4934_ = lean_st_ref_get(v___y_4932_);
v_env_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc_ref(v_env_4935_);
lean_dec(v___x_4934_);
v___f_4936_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4936_, 0, v_fnNames_4927_);
lean_closure_set(v___f_4936_, 1, v_numSectionVars_4928_);
lean_closure_set(v___f_4936_, 2, v_env_4935_);
v___x_4937_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4929_, v___f_4936_, v___f_4930_, v___y_4931_, v___y_4932_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_4938_, lean_object* v_numSectionVars_4939_, lean_object* v_e_4940_, lean_object* v___f_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_4938_, v_numSectionVars_4939_, v_e_4940_, v___f_4941_, v___y_4942_, v___y_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_4946_, uint8_t v_isExporting_4947_, lean_object* v___x_4948_, lean_object* v_a_x3f_4949_){
_start:
{
lean_object* v___x_4951_; lean_object* v_env_4952_; lean_object* v_nextMacroScope_4953_; lean_object* v_ngen_4954_; lean_object* v_auxDeclNGen_4955_; lean_object* v_traceState_4956_; lean_object* v_messages_4957_; lean_object* v_infoState_4958_; lean_object* v_snapshotTasks_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4970_; 
v___x_4951_ = lean_st_ref_take(v___y_4946_);
v_env_4952_ = lean_ctor_get(v___x_4951_, 0);
v_nextMacroScope_4953_ = lean_ctor_get(v___x_4951_, 1);
v_ngen_4954_ = lean_ctor_get(v___x_4951_, 2);
v_auxDeclNGen_4955_ = lean_ctor_get(v___x_4951_, 3);
v_traceState_4956_ = lean_ctor_get(v___x_4951_, 4);
v_messages_4957_ = lean_ctor_get(v___x_4951_, 6);
v_infoState_4958_ = lean_ctor_get(v___x_4951_, 7);
v_snapshotTasks_4959_ = lean_ctor_get(v___x_4951_, 8);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4970_ == 0)
{
lean_object* v_unused_4971_; 
v_unused_4971_ = lean_ctor_get(v___x_4951_, 5);
lean_dec(v_unused_4971_);
v___x_4961_ = v___x_4951_;
v_isShared_4962_ = v_isSharedCheck_4970_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_snapshotTasks_4959_);
lean_inc(v_infoState_4958_);
lean_inc(v_messages_4957_);
lean_inc(v_traceState_4956_);
lean_inc(v_auxDeclNGen_4955_);
lean_inc(v_ngen_4954_);
lean_inc(v_nextMacroScope_4953_);
lean_inc(v_env_4952_);
lean_dec(v___x_4951_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4970_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4963_ = l_Lean_Environment_setExporting(v_env_4952_, v_isExporting_4947_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 5, v___x_4948_);
lean_ctor_set(v___x_4961_, 0, v___x_4963_);
v___x_4965_ = v___x_4961_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4963_);
lean_ctor_set(v_reuseFailAlloc_4969_, 1, v_nextMacroScope_4953_);
lean_ctor_set(v_reuseFailAlloc_4969_, 2, v_ngen_4954_);
lean_ctor_set(v_reuseFailAlloc_4969_, 3, v_auxDeclNGen_4955_);
lean_ctor_set(v_reuseFailAlloc_4969_, 4, v_traceState_4956_);
lean_ctor_set(v_reuseFailAlloc_4969_, 5, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4969_, 6, v_messages_4957_);
lean_ctor_set(v_reuseFailAlloc_4969_, 7, v_infoState_4958_);
lean_ctor_set(v_reuseFailAlloc_4969_, 8, v_snapshotTasks_4959_);
v___x_4965_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = lean_st_ref_set(v___y_4946_, v___x_4965_);
v___x_4967_ = lean_box(0);
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
return v___x_4968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_4972_, lean_object* v_isExporting_4973_, lean_object* v___x_4974_, lean_object* v_a_x3f_4975_, lean_object* v___y_4976_){
_start:
{
uint8_t v_isExporting_boxed_4977_; lean_object* v_res_4978_; 
v_isExporting_boxed_4977_ = lean_unbox(v_isExporting_4973_);
v_res_4978_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_4972_, v_isExporting_boxed_4977_, v___x_4974_, v_a_x3f_4975_);
lean_dec(v_a_x3f_4975_);
lean_dec(v___y_4972_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_4979_, uint8_t v_isExporting_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v___x_4984_; lean_object* v_env_4985_; uint8_t v_isExporting_4986_; lean_object* v___x_4987_; lean_object* v_env_4988_; lean_object* v_nextMacroScope_4989_; lean_object* v_ngen_4990_; lean_object* v_auxDeclNGen_4991_; lean_object* v_traceState_4992_; lean_object* v_messages_4993_; lean_object* v_infoState_4994_; lean_object* v_snapshotTasks_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5034_; 
v___x_4984_ = lean_st_ref_get(v___y_4982_);
v_env_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc_ref(v_env_4985_);
lean_dec(v___x_4984_);
v_isExporting_4986_ = lean_ctor_get_uint8(v_env_4985_, sizeof(void*)*8);
lean_dec_ref(v_env_4985_);
v___x_4987_ = lean_st_ref_take(v___y_4982_);
v_env_4988_ = lean_ctor_get(v___x_4987_, 0);
v_nextMacroScope_4989_ = lean_ctor_get(v___x_4987_, 1);
v_ngen_4990_ = lean_ctor_get(v___x_4987_, 2);
v_auxDeclNGen_4991_ = lean_ctor_get(v___x_4987_, 3);
v_traceState_4992_ = lean_ctor_get(v___x_4987_, 4);
v_messages_4993_ = lean_ctor_get(v___x_4987_, 6);
v_infoState_4994_ = lean_ctor_get(v___x_4987_, 7);
v_snapshotTasks_4995_ = lean_ctor_get(v___x_4987_, 8);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5034_ == 0)
{
lean_object* v_unused_5035_; 
v_unused_5035_ = lean_ctor_get(v___x_4987_, 5);
lean_dec(v_unused_5035_);
v___x_4997_ = v___x_4987_;
v_isShared_4998_ = v_isSharedCheck_5034_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_snapshotTasks_4995_);
lean_inc(v_infoState_4994_);
lean_inc(v_messages_4993_);
lean_inc(v_traceState_4992_);
lean_inc(v_auxDeclNGen_4991_);
lean_inc(v_ngen_4990_);
lean_inc(v_nextMacroScope_4989_);
lean_inc(v_env_4988_);
lean_dec(v___x_4987_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5034_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_4999_ = l_Lean_Environment_setExporting(v_env_4988_, v_isExporting_4980_);
v___x_5000_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 5, v___x_5000_);
lean_ctor_set(v___x_4997_, 0, v___x_4999_);
v___x_5002_ = v___x_4997_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_4999_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v_nextMacroScope_4989_);
lean_ctor_set(v_reuseFailAlloc_5033_, 2, v_ngen_4990_);
lean_ctor_set(v_reuseFailAlloc_5033_, 3, v_auxDeclNGen_4991_);
lean_ctor_set(v_reuseFailAlloc_5033_, 4, v_traceState_4992_);
lean_ctor_set(v_reuseFailAlloc_5033_, 5, v___x_5000_);
lean_ctor_set(v_reuseFailAlloc_5033_, 6, v_messages_4993_);
lean_ctor_set(v_reuseFailAlloc_5033_, 7, v_infoState_4994_);
lean_ctor_set(v_reuseFailAlloc_5033_, 8, v_snapshotTasks_4995_);
v___x_5002_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
lean_object* v___x_5003_; lean_object* v_r_5004_; 
v___x_5003_ = lean_st_ref_set(v___y_4982_, v___x_5002_);
lean_inc(v___y_4982_);
v_r_5004_ = lean_apply_3(v_x_4979_, v___y_4981_, v___y_4982_, lean_box(0));
if (lean_obj_tag(v_r_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5021_; 
v_a_5005_ = lean_ctor_get(v_r_5004_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_r_5004_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5007_ = v_r_5004_;
v_isShared_5008_ = v_isSharedCheck_5021_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v_r_5004_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5021_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
lean_inc(v_a_5005_);
if (v_isShared_5008_ == 0)
{
lean_ctor_set_tag(v___x_5007_, 1);
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5018_; 
v___x_5011_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_4982_, v_isExporting_4986_, v___x_5000_, v___x_5010_);
lean_dec_ref(v___x_5010_);
lean_dec(v___y_4982_);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; 
v_unused_5019_ = lean_ctor_get(v___x_5011_, 0);
lean_dec(v_unused_5019_);
v___x_5013_ = v___x_5011_;
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
else
{
lean_dec(v___x_5011_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5016_; 
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 0, v_a_5005_);
v___x_5016_ = v___x_5013_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5005_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
v_a_5022_ = lean_ctor_get(v_r_5004_, 0);
lean_inc(v_a_5022_);
lean_dec_ref(v_r_5004_);
v___x_5023_ = lean_box(0);
v___x_5024_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_4982_, v_isExporting_4986_, v___x_5000_, v___x_5023_);
lean_dec(v___y_4982_);
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
lean_ctor_set(v___x_5026_, 0, v_a_5022_);
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5022_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5036_, lean_object* v_isExporting_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
uint8_t v_isExporting_boxed_5041_; lean_object* v_res_5042_; 
v_isExporting_boxed_5041_ = lean_unbox(v_isExporting_5037_);
v_res_5042_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5036_, v_isExporting_boxed_5041_, v___y_5038_, v___y_5039_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5043_, uint8_t v_when_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
if (v_when_5044_ == 0)
{
lean_object* v___x_5048_; 
v___x_5048_ = lean_apply_3(v_x_5043_, v___y_5045_, v___y_5046_, lean_box(0));
return v___x_5048_;
}
else
{
uint8_t v___x_5049_; lean_object* v___x_5050_; 
v___x_5049_ = 0;
v___x_5050_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5043_, v___x_5049_, v___y_5045_, v___y_5046_);
return v___x_5050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5051_, lean_object* v_when_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
uint8_t v_when_boxed_5056_; lean_object* v_res_5057_; 
v_when_boxed_5056_ = lean_unbox(v_when_5052_);
v_res_5057_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5051_, v_when_boxed_5056_, v___y_5053_, v___y_5054_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5058_, lean_object* v_numSectionVars_5059_, lean_object* v_e_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v___f_5064_; lean_object* v___f_5065_; uint8_t v___x_5066_; lean_object* v___x_5067_; 
v___f_5064_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5065_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5065_, 0, v_fnNames_5058_);
lean_closure_set(v___f_5065_, 1, v_numSectionVars_5059_);
lean_closure_set(v___f_5065_, 2, v_e_5060_);
lean_closure_set(v___f_5065_, 3, v___f_5064_);
v___x_5066_ = 1;
v___x_5067_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5065_, v___x_5066_, v_a_5061_, v_a_5062_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5068_, lean_object* v_numSectionVars_5069_, lean_object* v_e_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5068_, v_numSectionVars_5069_, v_e_5070_, v_a_5071_, v_a_5072_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5075_, lean_object* v_x_5076_, uint8_t v_isExporting_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5076_, v_isExporting_5077_, v___y_5078_, v___y_5079_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5082_, lean_object* v_x_5083_, lean_object* v_isExporting_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
uint8_t v_isExporting_boxed_5088_; lean_object* v_res_5089_; 
v_isExporting_boxed_5088_ = lean_unbox(v_isExporting_5084_);
v_res_5089_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5082_, v_x_5083_, v_isExporting_boxed_5088_, v___y_5085_, v___y_5086_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5090_, lean_object* v_x_5091_, uint8_t v_when_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v___x_5096_; 
v___x_5096_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5091_, v_when_5092_, v___y_5093_, v___y_5094_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5097_, lean_object* v_x_5098_, lean_object* v_when_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
uint8_t v_when_boxed_5103_; lean_object* v_res_5104_; 
v_when_boxed_5103_ = lean_unbox(v_when_5099_);
v_res_5104_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5097_, v_x_5098_, v_when_boxed_5103_, v___y_5100_, v___y_5101_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5111_, v___y_5112_, v___y_5113_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec_ref(v_x_5111_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v___y_5121_; lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_inaccessible_x3f(v_e_5116_);
if (lean_obj_tag(v___x_5124_) == 1)
{
lean_object* v_val_5125_; 
lean_dec_ref(v_e_5116_);
v_val_5125_ = lean_ctor_get(v___x_5124_, 0);
lean_inc(v_val_5125_);
lean_dec_ref(v___x_5124_);
v___y_5121_ = v_val_5125_;
goto v___jp_5120_;
}
else
{
lean_dec(v___x_5124_);
v___y_5121_ = v_e_5116_;
goto v___jp_5120_;
}
v___jp_5120_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v___y_5121_);
v___x_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5122_);
return v___x_5123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_){
_start:
{
lean_object* v___f_5137_; lean_object* v___f_5138_; lean_object* v___x_5139_; 
v___f_5137_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5138_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5139_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5133_, v___f_5137_, v___f_5138_, v_a_5134_, v_a_5135_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5140_, v_a_5141_, v_a_5142_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v___y_5150_; lean_object* v___x_5153_; 
v___x_5153_ = l_Lean_patternWithRef_x3f(v_e_5145_);
if (lean_obj_tag(v___x_5153_) == 1)
{
lean_object* v_val_5154_; lean_object* v_snd_5155_; 
lean_dec_ref(v_e_5145_);
v_val_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc(v_val_5154_);
lean_dec_ref(v___x_5153_);
v_snd_5155_ = lean_ctor_get(v_val_5154_, 1);
lean_inc(v_snd_5155_);
lean_dec(v_val_5154_);
v___y_5150_ = v_snd_5155_;
goto v___jp_5149_;
}
else
{
lean_dec(v___x_5153_);
v___y_5150_ = v_e_5145_;
goto v___jp_5149_;
}
v___jp_5149_:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5151_, 0, v___y_5150_);
v___x_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5151_);
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5156_, v___y_5157_, v___y_5158_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v___f_5166_; lean_object* v___f_5167_; lean_object* v___x_5168_; 
v___f_5166_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5167_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5168_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5162_, v___f_5166_, v___f_5167_, v_a_5163_, v_a_5164_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5169_, v_a_5170_, v_a_5171_);
return v_res_5173_;
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
