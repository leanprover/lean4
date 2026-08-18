// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: public import Lean.Meta.AppBuilder import Lean.ExtraModUses import Lean.Meta.WHNF
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "coe_decl"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 217, 140, 88, 250, 134, 204, 64)}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "auxiliary definition used to implement coercion (unfolded during elaboration)"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeDeclAttr"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 20, 115, 115, 128, 118, 26, 153)}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 308, .m_capacity = 308, .m_length = 307, .m_data = "Tags declarations to be unfolded during coercion elaboration.\n\nThis is mostly used to hide coercion implementation details and show the coerced result instead of\nan application of auxiliary definitions (e.g. `CoeT.coe`, `Coe.coe`). This attribute only works on\nreducible functions and instance projections.\n"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_expandCoe___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_expandCoe___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_expandCoe___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Coe"};
static const lean_object* l_Lean_Meta_expandCoe___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_expandCoe___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "coe"};
static const lean_object* l_Lean_Meta_expandCoe___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_expandCoe___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 70, 184, 182, 52, 50, 221, 222)}};
static const lean_ctor_object l_Lean_Meta_expandCoe___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 161, 101, 251, 53, 131, 233)}};
static const lean_object* l_Lean_Meta_expandCoe___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_expandCoe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_expandCoe___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_expandCoe___closed__0 = (const lean_object*)&l_Lean_Meta_expandCoe___closed__0_value;
static const lean_closure_object l_Lean_Meta_expandCoe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_expandCoe___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_expandCoe___closed__1 = (const lean_object*)&l_Lean_Meta_expandCoe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "autoLift"};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(168, 70, 99, 132, 14, 255, 243, 87)}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "Insert monadic lifts (i.e., `liftM` and coercions) when needed."};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(197, 184, 93, 140, 214, 99, 153, 189)}};
static const lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_autoLift;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CoeT"};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 0, 82, 253, 29, 221, 45, 84)}};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 0, 82, 253, 29, 221, 45, 84)}};
static const lean_ctor_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 80, 89, 153, 124, 3, 255, 77)}};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Could not coerce"};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4;
static const lean_string_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\nto"};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6;
static const lean_string_object l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "\ncoerced expression has wrong type:"};
static const lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_coerceToFunction_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "CoeFun"};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_coerceToFunction_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 121, 249, 91, 203, 193, 161, 225)}};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_coerceToFunction_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 121, 249, 91, 203, 193, 161, 225)}};
static const lean_ctor_object l_Lean_Meta_coerceToFunction_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 94, 101, 78, 118, 25, 69, 111)}};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_coerceToFunction_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to coerce"};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_coerceToFunction_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__4;
static const lean_string_object l_Lean_Meta_coerceToFunction_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "\nto a function: After applying `CoeFun.coe`, result is still not a function"};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_coerceToFunction_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__6;
static const lean_string_object l_Lean_Meta_coerceToFunction_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "This is often due to incorrect `CoeFun` instances; the synthesized instance was"};
static const lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_coerceToFunction_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_coerceToFunction_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceToFunction_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_coerceToSort_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CoeSort"};
static const lean_object* l_Lean_Meta_coerceToSort_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_coerceToSort_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 41, 56, 145, 201, 10, 66, 222)}};
static const lean_object* l_Lean_Meta_coerceToSort_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_coerceToSort_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 41, 56, 145, 201, 10, 66, 222)}};
static const lean_ctor_object l_Lean_Meta_coerceToSort_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_expandCoe___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(249, 65, 70, 162, 243, 253, 64, 246)}};
static const lean_object* l_Lean_Meta_coerceToSort_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_coerceToSort_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "\nto a type: After applying `CoeSort.coe`, result is still not a type"};
static const lean_object* l_Lean_Meta_coerceToSort_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_coerceToSort_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__4;
static const lean_string_object l_Lean_Meta_coerceToSort_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "This is often due to incorrect `CoeSort` instances; the synthesized instance was"};
static const lean_object* l_Lean_Meta_coerceToSort_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_coerceToSort_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_coerceToSort_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceToSort_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MonadLiftT"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 247, 249, 204, 219, 215, 23, 105)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "liftM"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 61, 106, 101, 51, 7, 16, 91)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_coerceMonadLift_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__6;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftCoeM"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__8_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 146, 186, 152, 132, 76, 197)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(59, 34, 101, 209, 97, 81, 138, 47)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "coeM"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 146, 186, 152, 132, 76, 197)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(21, 111, 129, 2, 187, 243, 141, 114)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_25_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_29_ = 0;
v___x_30_ = lean_box(2);
v___x_31_ = l_Lean_registerTagAttribute(v___x_26_, v___x_27_, v___f_25_, v___x_28_, v___x_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1(){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_37_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0));
v___x_38_ = l_Lean_addBuiltinDocString(v___x_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3(){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6));
v___x_69_ = l_Lean_addBuiltinDeclarationRanges(v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
return v_res_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isCoeDecl(lean_object* v_env_72_, lean_object* v_declName_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = l_Lean_Meta_coeDeclAttr;
v___x_75_ = l_Lean_TagAttribute_hasTag(v___x_74_, v_env_72_, v_declName_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isCoeDecl___boxed(lean_object* v_env_76_, lean_object* v_declName_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Meta_isCoeDecl(v_env_76_, v_declName_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(lean_object* v_declName_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_env_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_83_);
v___x_85_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_84_, v_declName_80_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg___boxed(lean_object* v_declName_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_87_, v___y_88_);
lean_dec(v___y_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(lean_object* v_declName_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_91_, v___y_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___boxed(lean_object* v_declName_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(v_declName_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = l_Lean_Expr_sort___override(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(lean_object* v_e_107_, lean_object* v_nm_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
lean_inc(v_nm_108_);
v___x_114_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_nm_108_, v_a_112_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_137_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_137_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
if (lean_obj_tag(v_a_115_) == 1)
{
lean_object* v_val_119_; lean_object* v_numParams_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_val_119_ = lean_ctor_get(v_a_115_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v_a_115_, 1);
v_numParams_120_ = lean_ctor_get(v_val_119_, 1);
lean_inc(v_numParams_120_);
lean_dec(v_val_119_);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v___x_122_ = l_Lean_Expr_getAppNumArgs(v_e_107_);
v___x_123_ = lean_nat_sub(v___x_122_, v_numParams_120_);
lean_dec(v_numParams_120_);
lean_dec(v___x_122_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_sub(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
v___x_126_ = l_Lean_Expr_getRevArgD(v_e_107_, v___x_125_, v___x_121_);
lean_dec_ref(v_e_107_);
v___x_127_ = l_Lean_Expr_getAppFn(v___x_126_);
v___x_128_ = l_Lean_Expr_isConst(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v___x_127_);
lean_dec_ref(v___x_126_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_nm_108_);
v___x_130_ = v___x_117_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_nm_108_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v___x_132_; 
lean_del_object(v___x_117_);
lean_dec(v_nm_108_);
v___x_132_ = l_Lean_Expr_constName_x21(v___x_127_);
lean_dec_ref(v___x_127_);
v_e_107_ = v___x_126_;
v_nm_108_ = v___x_132_;
goto _start;
}
}
else
{
lean_object* v___x_135_; 
lean_dec(v_a_115_);
lean_dec_ref(v_e_107_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_nm_108_);
v___x_135_ = v___x_117_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_nm_108_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_nm_108_);
lean_dec_ref(v_e_107_);
v_a_138_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_114_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_114_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___boxed(lean_object* v_e_146_, lean_object* v_nm_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_146_, v_nm_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0(lean_object* v_e_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v_e_154_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___y_155_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__0___boxed(lean_object* v_e_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_expandCoe___lam__0(v_e_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v_env_179_; lean_object* v___x_180_; lean_object* v_mctx_181_; lean_object* v_lctx_182_; lean_object* v_options_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_st_ref_get(v___y_174_);
v_mctx_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_mctx_181_);
lean_dec(v___x_180_);
v_lctx_182_ = lean_ctor_get(v___y_173_, 2);
v_options_183_ = lean_ctor_get(v___y_175_, 2);
lean_inc_ref(v_options_183_);
lean_inc_ref(v_lctx_182_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_179_);
lean_ctor_set(v___x_184_, 1, v_mctx_181_);
lean_ctor_set(v___x_184_, 2, v_lctx_182_);
lean_ctor_set(v___x_184_, 3, v_options_183_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_172_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_194_; double v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_float_of_nat(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_ref_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_254_; 
v_ref_207_ = lean_ctor_get(v___y_204_, 5);
v___x_208_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_200_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_254_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_254_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_254_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v_traceState_214_; lean_object* v_env_215_; lean_object* v_nextMacroScope_216_; lean_object* v_ngen_217_; lean_object* v_auxDeclNGen_218_; lean_object* v_cache_219_; lean_object* v_messages_220_; lean_object* v_infoState_221_; lean_object* v_snapshotTasks_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_253_; 
v___x_213_ = lean_st_ref_take(v___y_205_);
v_traceState_214_ = lean_ctor_get(v___x_213_, 4);
v_env_215_ = lean_ctor_get(v___x_213_, 0);
v_nextMacroScope_216_ = lean_ctor_get(v___x_213_, 1);
v_ngen_217_ = lean_ctor_get(v___x_213_, 2);
v_auxDeclNGen_218_ = lean_ctor_get(v___x_213_, 3);
v_cache_219_ = lean_ctor_get(v___x_213_, 5);
v_messages_220_ = lean_ctor_get(v___x_213_, 6);
v_infoState_221_ = lean_ctor_get(v___x_213_, 7);
v_snapshotTasks_222_ = lean_ctor_get(v___x_213_, 8);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_253_ == 0)
{
v___x_224_ = v___x_213_;
v_isShared_225_ = v_isSharedCheck_253_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snapshotTasks_222_);
lean_inc(v_infoState_221_);
lean_inc(v_messages_220_);
lean_inc(v_cache_219_);
lean_inc(v_traceState_214_);
lean_inc(v_auxDeclNGen_218_);
lean_inc(v_ngen_217_);
lean_inc(v_nextMacroScope_216_);
lean_inc(v_env_215_);
lean_dec(v___x_213_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_253_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint64_t v_tid_226_; lean_object* v_traces_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_252_; 
v_tid_226_ = lean_ctor_get_uint64(v_traceState_214_, sizeof(void*)*1);
v_traces_227_ = lean_ctor_get(v_traceState_214_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_traceState_214_);
if (v_isSharedCheck_252_ == 0)
{
v___x_229_ = v_traceState_214_;
v_isShared_230_ = v_isSharedCheck_252_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_traces_227_);
lean_dec(v_traceState_214_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_252_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; double v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_231_ = lean_box(0);
v___x_232_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_233_ = 0;
v___x_234_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_235_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_235_, 0, v_cls_199_);
lean_ctor_set(v___x_235_, 1, v___x_231_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
lean_ctor_set_float(v___x_235_, sizeof(void*)*3, v___x_232_);
lean_ctor_set_float(v___x_235_, sizeof(void*)*3 + 8, v___x_232_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 16, v___x_233_);
v___x_236_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_237_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v_a_209_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_inc(v_ref_207_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_ref_207_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_PersistentArray_push___redArg(v_traces_227_, v___x_238_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_239_);
v___x_241_ = v___x_229_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_239_);
lean_ctor_set_uint64(v_reuseFailAlloc_251_, sizeof(void*)*1, v_tid_226_);
v___x_241_ = v_reuseFailAlloc_251_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 4, v___x_241_);
v___x_243_ = v___x_224_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_env_215_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_nextMacroScope_216_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_ngen_217_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_auxDeclNGen_218_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_250_, 5, v_cache_219_);
lean_ctor_set(v_reuseFailAlloc_250_, 6, v_messages_220_);
lean_ctor_set(v_reuseFailAlloc_250_, 7, v_infoState_221_);
lean_ctor_set(v_reuseFailAlloc_250_, 8, v_snapshotTasks_222_);
v___x_243_ = v_reuseFailAlloc_250_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_st_ref_put(v___y_205_, v___x_243_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_201_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_246_);
v___x_248_ = v___x_211_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_255_, v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_264_, lean_object* v_i_265_, lean_object* v_k_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_array_get_size(v_keys_264_);
v___x_268_ = lean_nat_dec_lt(v_i_265_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v_i_265_);
return v___x_268_;
}
else
{
lean_object* v_k_x27_269_; uint8_t v___x_270_; 
v_k_x27_269_ = lean_array_fget_borrowed(v_keys_264_, v_i_265_);
v___x_270_ = l_Lean_instBEqExtraModUse_beq(v_k_266_, v_k_x27_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_i_265_, v___x_271_);
lean_dec(v_i_265_);
v_i_265_ = v___x_272_;
goto _start;
}
else
{
lean_dec(v_i_265_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_274_, v_i_275_, v_k_276_);
lean_dec_ref(v_k_276_);
lean_dec_ref(v_keys_274_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_279_, size_t v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_es_282_; lean_object* v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v_j_286_; lean_object* v___x_287_; 
v_es_282_ = lean_ctor_get(v_x_279_, 0);
v___x_283_ = lean_box(2);
v___x_284_ = ((size_t)31ULL);
v___x_285_ = lean_usize_land(v_x_280_, v___x_284_);
v_j_286_ = lean_usize_to_nat(v___x_285_);
v___x_287_ = lean_array_get_borrowed(v___x_283_, v_es_282_, v_j_286_);
lean_dec(v_j_286_);
switch(lean_obj_tag(v___x_287_))
{
case 0:
{
lean_object* v_key_288_; uint8_t v___x_289_; 
v_key_288_ = lean_ctor_get(v___x_287_, 0);
v___x_289_ = l_Lean_instBEqExtraModUse_beq(v_x_281_, v_key_288_);
return v___x_289_;
}
case 1:
{
lean_object* v_node_290_; size_t v___x_291_; size_t v___x_292_; 
v_node_290_ = lean_ctor_get(v___x_287_, 0);
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_usize_shift_right(v_x_280_, v___x_291_);
v_x_279_ = v_node_290_;
v_x_280_ = v___x_292_;
goto _start;
}
default: 
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
}
}
else
{
lean_object* v_ks_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_ks_295_ = lean_ctor_get(v_x_279_, 0);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_295_, v___x_296_, v_x_281_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
size_t v_x_38808__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_38808__boxed_301_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_res_302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_298_, v_x_38808__boxed_301_, v_x_300_);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_x_298_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
uint64_t v___x_306_; size_t v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_Lean_instHashableExtraModUse_hash(v_x_305_);
v___x_307_ = lean_uint64_to_usize(v___x_306_);
v___x_308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_304_, v___x_307_, v_x_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_309_, v_x_310_);
lean_dec_ref(v_x_310_);
lean_dec_ref(v_x_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1));
v___x_316_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0));
v___x_317_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_324_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v___x_323_);
lean_ctor_set(v___x_324_, 3, v___x_323_);
lean_ctor_set(v___x_324_, 4, v___x_323_);
lean_ctor_set(v___x_324_, 5, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_335_ = l_Lean_stringToMessageData(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_cls_339_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_340_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_341_ = l_Lean_Name_append(v___x_340_, v_cls_339_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_352_, uint8_t v_isMeta_353_, lean_object* v_hint_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_env_362_; uint8_t v_isExporting_363_; lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v___x_366_; lean_object* v_entry_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_361_ = lean_st_ref_get(v___y_359_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v_isExporting_363_ = lean_ctor_get_uint8(v_env_362_, sizeof(void*)*8);
lean_dec_ref(v_env_362_);
v___x_364_ = lean_st_ref_get(v___y_359_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
lean_inc(v_mod_352_);
v_entry_367_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_367_, 0, v_mod_352_);
lean_ctor_set_uint8(v_entry_367_, sizeof(void*)*1, v_isExporting_363_);
lean_ctor_set_uint8(v_entry_367_, sizeof(void*)*1 + 1, v_isMeta_353_);
v___x_368_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_369_ = lean_box(1);
v___x_370_ = lean_box(0);
v___x_415_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_366_, v___x_368_, v_env_365_, v___x_369_, v___x_370_);
v___x_416_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_415_, v_entry_367_);
lean_dec(v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v_options_417_; uint8_t v_hasTrace_418_; 
v_options_417_ = lean_ctor_get(v___y_358_, 2);
v_hasTrace_418_ = lean_ctor_get_uint8(v_options_417_, sizeof(void*)*1);
if (v_hasTrace_418_ == 0)
{
lean_dec(v_hint_354_);
lean_dec(v_mod_352_);
v___y_372_ = v___y_355_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_359_;
goto v___jp_371_;
}
else
{
lean_object* v_inheritedTraceOptions_419_; lean_object* v_cls_420_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_inheritedTraceOptions_419_ = lean_ctor_get(v___y_358_, 13);
v_cls_420_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_443_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_419_, v_options_417_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v_hint_354_);
lean_dec(v_mod_352_);
v___y_372_ = v___y_355_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_359_;
goto v___jp_371_;
}
else
{
lean_object* v___x_444_; lean_object* v___y_446_; 
v___x_444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_363_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_446_ = v___x_453_;
goto v___jp_445_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_446_ = v___x_454_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref(v___y_446_);
v___x_447_ = l_Lean_stringToMessageData(v___y_446_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
if (v_isMeta_353_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_429_ = v___x_450_;
v___y_430_ = v___x_451_;
goto v___jp_428_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_429_ = v___x_450_;
v___y_430_ = v___x_452_;
goto v___jp_428_;
}
}
}
v___jp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___y_422_);
lean_ctor_set(v___x_424_, 1, v___y_423_);
v___x_425_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_420_, v___x_424_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_snd_427_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v_snd_427_ = lean_ctor_get(v_a_426_, 1);
lean_inc(v_snd_427_);
lean_dec(v_a_426_);
v___y_372_ = v_snd_427_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_359_;
goto v___jp_371_;
}
else
{
lean_dec_ref_known(v_entry_367_, 1);
return v___x_425_;
}
}
v___jp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
lean_inc_ref(v___y_430_);
v___x_431_ = l_Lean_stringToMessageData(v___y_430_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___y_429_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_MessageData_ofName(v_mod_352_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_Name_isAnonymous(v_hint_354_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_439_ = l_Lean_MessageData_ofName(v_hint_354_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___y_422_ = v___x_436_;
v___y_423_ = v___x_440_;
goto v___jp_421_;
}
else
{
lean_object* v___x_441_; 
lean_dec(v_hint_354_);
v___x_441_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_422_ = v___x_436_;
v___y_423_ = v___x_441_;
goto v___jp_421_;
}
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref_known(v_entry_367_, 1);
lean_dec(v_hint_354_);
lean_dec(v_mod_352_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_355_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
v___jp_371_:
{
lean_object* v___x_375_; lean_object* v_toEnvExtension_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_traceState_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_413_; 
v___x_375_ = lean_st_ref_take(v___y_374_);
v_toEnvExtension_376_ = lean_ctor_get(v___x_368_, 0);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
v_traceState_381_ = lean_ctor_get(v___x_375_, 4);
v_messages_382_ = lean_ctor_get(v___x_375_, 6);
v_infoState_383_ = lean_ctor_get(v___x_375_, 7);
v_snapshotTasks_384_ = lean_ctor_get(v___x_375_, 8);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_375_, 5);
lean_dec(v_unused_414_);
v___x_386_ = v___x_375_;
v_isShared_387_ = v_isSharedCheck_413_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_traceState_381_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_413_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_asyncMode_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v_asyncMode_388_ = lean_ctor_get(v_toEnvExtension_376_, 2);
v___x_389_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_368_, v_env_377_, v_entry_367_, v_asyncMode_388_, v___x_370_);
v___x_390_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 5, v___x_390_);
lean_ctor_set(v___x_386_, 0, v___x_389_);
v___x_392_ = v___x_386_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_traceState_381_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_messages_382_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_snapshotTasks_384_);
v___x_392_ = v_reuseFailAlloc_412_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_mctx_395_; lean_object* v_zetaDeltaFVarIds_396_; lean_object* v_postponed_397_; lean_object* v_diag_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v___x_393_ = lean_st_ref_put(v___y_374_, v___x_392_);
v___x_394_ = lean_st_ref_take(v___y_373_);
v_mctx_395_ = lean_ctor_get(v___x_394_, 0);
v_zetaDeltaFVarIds_396_ = lean_ctor_get(v___x_394_, 2);
v_postponed_397_ = lean_ctor_get(v___x_394_, 3);
v_diag_398_ = lean_ctor_get(v___x_394_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_394_, 1);
lean_dec(v_unused_411_);
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_diag_398_);
lean_inc(v_postponed_397_);
lean_inc(v_zetaDeltaFVarIds_396_);
lean_inc(v_mctx_395_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_mctx_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_zetaDeltaFVarIds_396_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_postponed_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_diag_398_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_st_ref_put(v___y_373_, v___x_404_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___y_372_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_458_, lean_object* v_isMeta_459_, lean_object* v_hint_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v_isMeta_boxed_467_; lean_object* v_res_468_; 
v_isMeta_boxed_467_ = lean_unbox(v_isMeta_459_);
v_res_468_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_458_, v_isMeta_boxed_467_, v_hint_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_m_469_, lean_object* v_query_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_zero_474_; uint8_t v_isZero_475_; 
v_zero_474_ = lean_unsigned_to_nat(0u);
v_isZero_475_ = lean_nat_dec_eq(v_x_472_, v_zero_474_);
if (v_isZero_475_ == 1)
{
lean_dec(v_x_473_);
lean_dec(v_x_472_);
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_box(2);
return v___x_476_;
}
else
{
lean_object* v_val_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_val_477_ = lean_ctor_get(v_x_471_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v_x_471_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_val_477_);
lean_dec(v_x_471_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_val_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_keyArray_485_; lean_object* v_valueArray_486_; lean_object* v___x_487_; uint8_t v_isSome_488_; 
v_keyArray_485_ = lean_ctor_get(v_m_469_, 1);
v_valueArray_486_ = lean_ctor_get(v_m_469_, 2);
v___x_487_ = lean_array_fget_borrowed(v_keyArray_485_, v_x_473_);
v_isSome_488_ = lean_noption_is_some(v___x_487_);
if (v_isSome_488_ == 0)
{
lean_dec(v_x_472_);
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_x_473_);
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_x_473_);
v_val_490_ = lean_ctor_get(v_x_471_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_471_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v_x_471_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v_x_471_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_val_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_one_498_; lean_object* v_n_499_; lean_object* v___y_501_; 
v_one_498_ = lean_unsigned_to_nat(1u);
v_n_499_ = lean_nat_sub(v_x_472_, v_one_498_);
lean_dec(v_x_472_);
if (v_isSome_488_ == 0)
{
goto v___jp_507_;
}
else
{
lean_object* v___x_509_; uint8_t v_isSome_510_; 
v___x_509_ = lean_array_fget_borrowed(v_valueArray_486_, v_x_473_);
v_isSome_510_ = lean_noption_is_some(v___x_509_);
if (v_isSome_510_ == 0)
{
goto v___jp_507_;
}
else
{
lean_object* v_val_511_; uint8_t v___x_512_; 
lean_inc(v___x_487_);
v_val_511_ = lean_noption_get(v___x_487_);
v___x_512_ = lean_name_eq(v_val_511_, v_query_470_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
lean_dec(v_val_511_);
v___x_513_ = lean_array_get_size(v_keyArray_485_);
v___x_514_ = lean_nat_add(v_x_473_, v_one_498_);
lean_dec(v_x_473_);
v___x_515_ = lean_nat_dec_lt(v___x_514_, v___x_513_);
if (v___x_515_ == 0)
{
lean_dec(v___x_514_);
v_x_472_ = v_n_499_;
v_x_473_ = v_zero_474_;
goto _start;
}
else
{
v_x_472_ = v_n_499_;
v_x_473_ = v___x_514_;
goto _start;
}
}
else
{
lean_object* v_val_518_; lean_object* v___x_519_; 
lean_dec(v_n_499_);
lean_dec(v_x_471_);
lean_inc(v___x_509_);
v_val_518_ = lean_noption_get(v___x_509_);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v_x_473_);
lean_ctor_set(v___x_519_, 1, v_val_511_);
lean_ctor_set(v___x_519_, 2, v_val_518_);
return v___x_519_;
}
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_array_get_size(v_keyArray_485_);
v___x_503_ = lean_nat_add(v_x_473_, v_one_498_);
lean_dec(v_x_473_);
v___x_504_ = lean_nat_dec_lt(v___x_503_, v___x_502_);
if (v___x_504_ == 0)
{
lean_dec(v___x_503_);
v_x_471_ = v___y_501_;
v_x_472_ = v_n_499_;
v_x_473_ = v_zero_474_;
goto _start;
}
else
{
v_x_471_ = v___y_501_;
v_x_472_ = v_n_499_;
v_x_473_ = v___x_503_;
goto _start;
}
}
v___jp_507_:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_508_; 
lean_inc(v_x_473_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_x_473_);
v___y_501_ = v___x_508_;
goto v___jp_500_;
}
else
{
v___y_501_ = v_x_471_;
goto v___jp_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_m_520_, lean_object* v_query_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg(v_m_520_, v_query_521_, v_x_522_, v_x_523_, v_x_524_);
lean_dec(v_query_521_);
lean_dec_ref(v_m_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg(lean_object* v_m_526_, lean_object* v_query_527_){
_start:
{
lean_object* v_keyArray_528_; lean_object* v___x_529_; uint64_t v___y_531_; 
v_keyArray_528_ = lean_ctor_get(v_m_526_, 1);
v___x_529_ = lean_array_get_size(v_keyArray_528_);
if (lean_obj_tag(v_query_527_) == 0)
{
uint64_t v___x_546_; 
v___x_546_ = 1723ULL;
v___y_531_ = v___x_546_;
goto v___jp_530_;
}
else
{
uint64_t v_hash_547_; 
v_hash_547_ = lean_ctor_get_uint64(v_query_527_, sizeof(void*)*2);
v___y_531_ = v_hash_547_;
goto v___jp_530_;
}
v___jp_530_:
{
uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v_fold_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_532_ = 32ULL;
v___x_533_ = lean_uint64_shift_right(v___y_531_, v___x_532_);
v_fold_534_ = lean_uint64_xor(v___y_531_, v___x_533_);
v___x_535_ = 16ULL;
v___x_536_ = lean_uint64_shift_right(v_fold_534_, v___x_535_);
v___x_537_ = lean_uint64_xor(v_fold_534_, v___x_536_);
v___x_538_ = lean_uint64_to_usize(v___x_537_);
v___x_539_ = lean_usize_of_nat(v___x_529_);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_sub(v___x_539_, v___x_540_);
v___x_542_ = lean_usize_land(v___x_538_, v___x_541_);
v___x_543_ = lean_usize_to_nat(v___x_542_);
v___x_544_ = lean_box(0);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg(v_m_526_, v_query_527_, v___x_544_, v___x_529_, v___x_543_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_m_548_, lean_object* v_query_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg(v_m_548_, v_query_549_);
lean_dec(v_query_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_m_551_, lean_object* v_query_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg(v_m_551_, v_query_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_index_554_; lean_object* v_key_555_; lean_object* v_value_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_index_554_ = lean_ctor_get(v___x_553_, 0);
v_key_555_ = lean_ctor_get(v___x_553_, 1);
v_value_556_ = lean_ctor_get(v___x_553_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_key_555_);
lean_inc(v_index_554_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_index_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_key_555_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_value_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v___x_553_);
v___x_564_ = lean_box(1);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_565_, lean_object* v_query_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_m_565_, v_query_566_);
lean_dec(v_query_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_m_568_, v_a_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_value_571_; lean_object* v___x_572_; 
v_value_571_ = lean_ctor_get(v___x_570_, 2);
lean_inc(v_value_571_);
lean_dec_ref_known(v___x_570_, 3);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_value_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_box(0);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_m_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_577_, lean_object* v_declName_578_, lean_object* v_as_579_, size_t v_sz_580_, size_t v_i_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_lt(v_i_581_, v_sz_580_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_declName_578_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_b_582_);
lean_ctor_set(v___x_590_, 1, v___y_583_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v_modules_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v_toImport_597_; lean_object* v_module_598_; uint8_t v___x_599_; lean_object* v___x_600_; 
v___x_592_ = l_Lean_Environment_header(v___x_577_);
v_modules_593_ = lean_ctor_get(v___x_592_, 3);
lean_inc_ref(v_modules_593_);
lean_dec_ref(v___x_592_);
v___x_594_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_595_ = lean_array_uget_borrowed(v_as_579_, v_i_581_);
v___x_596_ = lean_array_get(v___x_594_, v_modules_593_, v_a_595_);
lean_dec_ref(v_modules_593_);
v_toImport_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc_ref(v_toImport_597_);
lean_dec(v___x_596_);
v_module_598_ = lean_ctor_get(v_toImport_597_, 0);
lean_inc(v_module_598_);
lean_dec_ref(v_toImport_597_);
v___x_599_ = 0;
lean_inc(v_declName_578_);
v___x_600_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_598_, v___x_599_, v_declName_578_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_snd_602_; lean_object* v___x_603_; size_t v___x_604_; size_t v___x_605_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v_snd_602_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_snd_602_);
lean_dec(v_a_601_);
v___x_603_ = lean_box(0);
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_581_, v___x_604_);
v_i_581_ = v___x_605_;
v_b_582_ = v___x_603_;
v___y_583_ = v_snd_602_;
goto _start;
}
else
{
lean_dec(v_declName_578_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_607_, lean_object* v_declName_608_, lean_object* v_as_609_, lean_object* v_sz_610_, lean_object* v_i_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_610_);
lean_dec(v_sz_610_);
v_i_boxed_620_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_607_, v_declName_608_, v_as_609_, v_sz_boxed_619_, v_i_boxed_620_, v_b_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec_ref(v_as_609_);
lean_dec_ref(v___x_607_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_625_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_626_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_625_, v___x_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_629_, uint8_t v_isMeta_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_env_642_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___x_667_; 
v___x_637_ = lean_st_ref_get(v___y_635_);
v_env_642_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_642_);
lean_dec(v___x_637_);
v___x_667_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_642_, v_declName_629_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref(v_env_642_);
lean_dec(v_declName_629_);
goto v___jp_638_;
}
else
{
lean_object* v_val_668_; lean_object* v___x_669_; lean_object* v_modules_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_Environment_header(v_env_642_);
v_modules_670_ = lean_ctor_get(v___x_669_, 3);
lean_inc_ref(v_modules_670_);
lean_dec_ref(v___x_669_);
v___x_671_ = lean_array_get_size(v_modules_670_);
v___x_672_ = lean_nat_dec_lt(v_val_668_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_modules_670_);
lean_dec(v_val_668_);
lean_dec_ref(v_env_642_);
lean_dec(v_declName_629_);
goto v___jp_638_;
}
else
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___y_678_; 
v___x_673_ = lean_st_ref_get(v___y_635_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_673_);
v___x_675_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_676_ = lean_array_fget(v_modules_670_, v_val_668_);
lean_dec(v_val_668_);
lean_dec_ref(v_modules_670_);
if (v_isMeta_630_ == 0)
{
lean_dec_ref(v_env_674_);
v___y_678_ = v_isMeta_630_;
goto v___jp_677_;
}
else
{
uint8_t v___x_691_; 
lean_inc(v_declName_629_);
v___x_691_ = l_Lean_isMarkedMeta(v_env_674_, v_declName_629_);
if (v___x_691_ == 0)
{
v___y_678_ = v_isMeta_630_;
goto v___jp_677_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 0;
v___y_678_ = v___x_692_;
goto v___jp_677_;
}
}
v___jp_677_:
{
lean_object* v_toImport_679_; lean_object* v_module_680_; lean_object* v___x_681_; 
v_toImport_679_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_toImport_679_);
lean_dec(v___x_676_);
v_module_680_ = lean_ctor_get(v_toImport_679_, 0);
lean_inc(v_module_680_);
lean_dec_ref(v_toImport_679_);
lean_inc(v_declName_629_);
v___x_681_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_680_, v___y_678_, v_declName_629_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_snd_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v_snd_683_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_683_);
lean_dec(v_a_682_);
v___x_684_ = l_Lean_indirectModUseExt;
v___x_685_ = lean_box(1);
v___x_686_ = lean_box(0);
lean_inc_ref(v_env_642_);
v___x_687_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_675_, v___x_684_, v_env_642_, v___x_685_, v___x_686_);
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_687_, v_declName_629_);
lean_dec(v___x_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_644_ = v_snd_683_;
v___y_645_ = v___x_689_;
goto v___jp_643_;
}
else
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_688_, 1);
v___y_644_ = v_snd_683_;
v___y_645_ = v_val_690_;
goto v___jp_643_;
}
}
else
{
lean_dec_ref(v_env_642_);
lean_dec(v_declName_629_);
return v___x_681_;
}
}
}
}
v___jp_638_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___y_631_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
v___jp_643_:
{
lean_object* v___x_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_646_ = lean_box(0);
v_sz_647_ = lean_array_size(v___y_645_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_642_, v_declName_629_, v___y_645_, v_sz_647_, v___x_648_, v___x_646_, v___y_644_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v_env_642_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_666_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_666_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_666_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_666_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_snd_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_664_; 
v_snd_654_ = lean_ctor_get(v_a_650_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_650_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_a_650_, 0);
lean_dec(v_unused_665_);
v___x_656_ = v_a_650_;
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_654_);
lean_dec(v_a_650_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_646_);
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_snd_654_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_659_);
v___x_661_ = v___x_652_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
else
{
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_693_, lean_object* v_isMeta_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v_isMeta_boxed_701_; lean_object* v_res_702_; 
v_isMeta_boxed_701_ = lean_unbox(v_isMeta_694_);
v_res_702_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_693_, v_isMeta_boxed_701_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___y_718_; lean_object* v_f_722_; uint8_t v___x_723_; 
v_f_722_ = l_Lean_Expr_getAppFn(v_e_710_);
v___x_723_ = l_Lean_Expr_isConst(v_f_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v_f_722_);
lean_dec_ref(v_e_710_);
v___y_718_ = v___y_711_;
goto v___jp_717_;
}
else
{
lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v_declName_726_; uint8_t v___x_727_; 
v___x_724_ = lean_st_ref_get(v___y_715_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_725_);
lean_dec(v___x_724_);
v_declName_726_ = l_Lean_Expr_constName_x21(v_f_722_);
lean_dec_ref(v_f_722_);
lean_inc(v_declName_726_);
v___x_727_ = l_Lean_Meta_isCoeDecl(v_env_725_, v_declName_726_);
if (v___x_727_ == 0)
{
lean_dec(v_declName_726_);
lean_dec_ref(v_e_710_);
v___y_718_ = v___y_711_;
goto v___jp_717_;
}
else
{
lean_object* v___x_728_; 
lean_inc(v_declName_726_);
lean_inc_ref(v_e_710_);
v___x_728_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_710_, v_declName_726_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = 0;
v___x_731_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_729_, v___x_730_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_784_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v_snd_733_ = lean_ctor_get(v_a_732_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_a_732_, 0);
lean_dec(v_unused_785_);
v___x_735_ = v_a_732_;
v_isShared_736_ = v_isSharedCheck_784_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_dec(v_a_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_784_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; 
lean_inc_ref(v_e_710_);
v___x_737_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_710_, v___x_730_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_775_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_775_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_775_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_775_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_a_738_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_774_; 
v_val_742_ = lean_ctor_get(v_a_738_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_774_ == 0)
{
v___x_744_ = v_a_738_;
v_isShared_745_ = v_isSharedCheck_774_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_a_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_774_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___y_747_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_759_ = lean_name_eq(v_declName_726_, v___x_758_);
lean_dec(v_declName_726_);
if (v___x_759_ == 0)
{
lean_dec_ref(v_e_710_);
v___y_747_ = v_snd_733_;
goto v___jp_746_;
}
else
{
lean_object* v_dummy_760_; lean_object* v_nargs_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_dummy_760_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_761_ = l_Lean_Expr_getAppNumArgs(v_e_710_);
lean_inc(v_nargs_761_);
v___x_762_ = lean_mk_array(v_nargs_761_, v_dummy_760_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_sub(v_nargs_761_, v___x_763_);
lean_dec(v_nargs_761_);
v___x_765_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_710_, v___x_762_, v___x_764_);
v___x_766_ = lean_unsigned_to_nat(2u);
v___x_767_ = lean_array_get_size(v___x_765_);
v___x_768_ = lean_nat_dec_lt(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec_ref(v___x_765_);
v___y_747_ = v_snd_733_;
goto v___jp_746_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_fget(v___x_765_, v___x_766_);
lean_dec_ref(v___x_765_);
v___x_770_ = l_Lean_Expr_getAppFn(v___x_769_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Expr_isConst(v___x_770_);
if (v___x_771_ == 0)
{
lean_dec_ref(v___x_770_);
v___y_747_ = v_snd_733_;
goto v___jp_746_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = l_Lean_Expr_constName_x21(v___x_770_);
lean_dec_ref(v___x_770_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_snd_733_);
v___y_747_ = v___x_773_;
goto v___jp_746_;
}
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = l_Lean_Expr_headBeta(v_val_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_750_ = v___x_744_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_757_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___y_747_);
lean_ctor_set(v___x_735_, 0, v___x_750_);
v___x_752_ = v___x_735_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___y_747_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_752_);
v___x_754_ = v___x_740_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_740_);
lean_dec(v_a_738_);
lean_del_object(v___x_735_);
lean_dec(v_declName_726_);
lean_dec_ref(v_e_710_);
v___y_718_ = v_snd_733_;
goto v___jp_717_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_del_object(v___x_735_);
lean_dec(v_snd_733_);
lean_dec(v_declName_726_);
lean_dec_ref(v_e_710_);
v_a_776_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_737_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_737_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_declName_726_);
lean_dec_ref(v_e_710_);
v_a_786_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_731_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_731_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_declName_726_);
lean_dec(v___y_711_);
lean_dec_ref(v_e_710_);
v_a_794_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_728_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_728_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___y_718_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_expandCoe___lam__1(v_e_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0(lean_object* v_k_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_811_);
v___x_819_ = lean_apply_8(v_k_810_, v_b_813_, v___y_811_, v___y_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0___boxed(lean_object* v_k_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0(v_k_820_, v___y_821_, v___y_822_, v_b_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_821_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(lean_object* v_name_830_, uint8_t v_bi_831_, lean_object* v_type_832_, lean_object* v_k_833_, uint8_t v_kind_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___f_842_; lean_object* v___x_843_; 
lean_inc(v___y_835_);
v___f_842_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_842_, 0, v_k_833_);
lean_closure_set(v___f_842_, 1, v___y_835_);
lean_closure_set(v___f_842_, 2, v___y_836_);
v___x_843_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_830_, v_bi_831_, v_type_832_, v___f_842_, v_kind_834_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___boxed(lean_object* v_name_860_, lean_object* v_bi_861_, lean_object* v_type_862_, lean_object* v_k_863_, lean_object* v_kind_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_bi_boxed_872_; uint8_t v_kind_boxed_873_; lean_object* v_res_874_; 
v_bi_boxed_872_ = lean_unbox(v_bi_861_);
v_kind_boxed_873_ = lean_unbox(v_kind_864_);
v_res_874_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(v_name_860_, v_bi_boxed_872_, v_type_862_, v_k_863_, v_kind_boxed_873_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_865_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_875_);
lean_ctor_set(v___x_882_, 1, v___y_876_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg(lean_object* v_name_892_, lean_object* v_type_893_, lean_object* v_val_894_, lean_object* v_k_895_, uint8_t v_nondep_896_, uint8_t v_kind_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___f_905_; lean_object* v___x_906_; 
lean_inc(v___y_898_);
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_905_, 0, v_k_895_);
lean_closure_set(v___f_905_, 1, v___y_898_);
lean_closure_set(v___f_905_, 2, v___y_899_);
v___x_906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_892_, v_type_893_, v_val_894_, v___f_905_, v_nondep_896_, v_kind_897_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_a_915_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_906_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_906_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg___boxed(lean_object* v_name_923_, lean_object* v_type_924_, lean_object* v_val_925_, lean_object* v_k_926_, lean_object* v_nondep_927_, lean_object* v_kind_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v_nondep_boxed_936_; uint8_t v_kind_boxed_937_; lean_object* v_res_938_; 
v_nondep_boxed_936_ = lean_unbox(v_nondep_927_);
v_kind_boxed_937_ = lean_unbox(v_kind_928_);
v_res_938_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg(v_name_923_, v_type_924_, v_val_925_, v_k_926_, v_nondep_boxed_936_, v_kind_boxed_937_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_929_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = l_Lean_maxRecDepthErrorMessage;
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__3);
v___x_947_ = l_Lean_MessageData_ofFormat(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__4);
v___x_949_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__2));
v___x_950_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg(lean_object* v_ref_951_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___closed__5);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_ref_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg___boxed(lean_object* v_ref_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg(v_ref_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___y_968_; lean_object* v_fileName_985_; lean_object* v_fileMap_986_; lean_object* v_options_987_; lean_object* v_currRecDepth_988_; lean_object* v_maxRecDepth_989_; lean_object* v_ref_990_; lean_object* v_currNamespace_991_; lean_object* v_openDecls_992_; lean_object* v_initHeartbeats_993_; lean_object* v_maxHeartbeats_994_; lean_object* v_quotContext_995_; lean_object* v_currMacroScope_996_; uint8_t v_diag_997_; lean_object* v_cancelTk_x3f_998_; uint8_t v_suppressElabErrors_999_; lean_object* v_inheritedTraceOptions_1000_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_fileName_985_ = lean_ctor_get(v___y_964_, 0);
v_fileMap_986_ = lean_ctor_get(v___y_964_, 1);
v_options_987_ = lean_ctor_get(v___y_964_, 2);
v_currRecDepth_988_ = lean_ctor_get(v___y_964_, 3);
v_maxRecDepth_989_ = lean_ctor_get(v___y_964_, 4);
v_ref_990_ = lean_ctor_get(v___y_964_, 5);
v_currNamespace_991_ = lean_ctor_get(v___y_964_, 6);
v_openDecls_992_ = lean_ctor_get(v___y_964_, 7);
v_initHeartbeats_993_ = lean_ctor_get(v___y_964_, 8);
v_maxHeartbeats_994_ = lean_ctor_get(v___y_964_, 9);
v_quotContext_995_ = lean_ctor_get(v___y_964_, 10);
v_currMacroScope_996_ = lean_ctor_get(v___y_964_, 11);
v_diag_997_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*14);
v_cancelTk_x3f_998_ = lean_ctor_get(v___y_964_, 12);
v_suppressElabErrors_999_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1000_ = lean_ctor_get(v___y_964_, 13);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_eq(v_maxRecDepth_989_, v___x_1006_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_eq(v_currRecDepth_988_, v_maxRecDepth_989_);
if (v___x_1008_ == 0)
{
goto v___jp_1001_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v___y_961_);
lean_dec_ref(v_x_959_);
lean_inc(v_ref_990_);
v___x_1009_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg(v_ref_990_);
v___y_968_ = v___x_1009_;
goto v___jp_967_;
}
}
else
{
goto v___jp_1001_;
}
v___jp_967_:
{
if (lean_obj_tag(v___y_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___y_968_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___y_968_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___y_968_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___y_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_a_977_ = lean_ctor_get(v___y_968_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___y_968_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___y_968_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___y_968_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
v___jp_1001_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_currRecDepth_988_, v___x_1002_);
lean_inc_ref(v_inheritedTraceOptions_1000_);
lean_inc(v_cancelTk_x3f_998_);
lean_inc(v_currMacroScope_996_);
lean_inc(v_quotContext_995_);
lean_inc(v_maxHeartbeats_994_);
lean_inc(v_initHeartbeats_993_);
lean_inc(v_openDecls_992_);
lean_inc(v_currNamespace_991_);
lean_inc(v_ref_990_);
lean_inc(v_maxRecDepth_989_);
lean_inc_ref(v_options_987_);
lean_inc_ref(v_fileMap_986_);
lean_inc_ref(v_fileName_985_);
v___x_1004_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1004_, 0, v_fileName_985_);
lean_ctor_set(v___x_1004_, 1, v_fileMap_986_);
lean_ctor_set(v___x_1004_, 2, v_options_987_);
lean_ctor_set(v___x_1004_, 3, v___x_1003_);
lean_ctor_set(v___x_1004_, 4, v_maxRecDepth_989_);
lean_ctor_set(v___x_1004_, 5, v_ref_990_);
lean_ctor_set(v___x_1004_, 6, v_currNamespace_991_);
lean_ctor_set(v___x_1004_, 7, v_openDecls_992_);
lean_ctor_set(v___x_1004_, 8, v_initHeartbeats_993_);
lean_ctor_set(v___x_1004_, 9, v_maxHeartbeats_994_);
lean_ctor_set(v___x_1004_, 10, v_quotContext_995_);
lean_ctor_set(v___x_1004_, 11, v_currMacroScope_996_);
lean_ctor_set(v___x_1004_, 12, v_cancelTk_x3f_998_);
lean_ctor_set(v___x_1004_, 13, v_inheritedTraceOptions_1000_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*14, v_diag_997_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*14 + 1, v_suppressElabErrors_999_);
lean_inc(v___y_965_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_960_);
v___x_1005_ = lean_apply_7(v_x_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___x_1004_, v___y_965_, lean_box(0));
v___y_968_ = v___x_1005_;
goto v___jp_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_m_1019_, lean_object* v_query_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v_zero_1024_; uint8_t v_isZero_1025_; 
v_zero_1024_ = lean_unsigned_to_nat(0u);
v_isZero_1025_ = lean_nat_dec_eq(v_x_1022_, v_zero_1024_);
if (v_isZero_1025_ == 1)
{
lean_dec(v_x_1023_);
lean_dec(v_x_1022_);
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_box(2);
return v___x_1026_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_val_1027_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v_x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_val_1027_);
lean_dec(v_x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_val_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_keyArray_1035_; lean_object* v_valueArray_1036_; lean_object* v___x_1037_; uint8_t v_isSome_1038_; 
v_keyArray_1035_ = lean_ctor_get(v_m_1019_, 1);
v_valueArray_1036_ = lean_ctor_get(v_m_1019_, 2);
v___x_1037_ = lean_array_fget_borrowed(v_keyArray_1035_, v_x_1023_);
v_isSome_1038_ = lean_noption_is_some(v___x_1037_);
if (v_isSome_1038_ == 0)
{
lean_dec(v_x_1022_);
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_x_1023_);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_x_1023_);
v_val_1040_ = lean_ctor_get(v_x_1021_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v_x_1021_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_x_1021_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_one_1048_; lean_object* v_n_1049_; lean_object* v___y_1051_; 
v_one_1048_ = lean_unsigned_to_nat(1u);
v_n_1049_ = lean_nat_sub(v_x_1022_, v_one_1048_);
lean_dec(v_x_1022_);
if (v_isSome_1038_ == 0)
{
goto v___jp_1057_;
}
else
{
lean_object* v___x_1059_; uint8_t v_isSome_1060_; 
v___x_1059_ = lean_array_fget_borrowed(v_valueArray_1036_, v_x_1023_);
v_isSome_1060_ = lean_noption_is_some(v___x_1059_);
if (v_isSome_1060_ == 0)
{
goto v___jp_1057_;
}
else
{
lean_object* v_val_1061_; uint8_t v___x_1062_; 
lean_inc(v___x_1037_);
v_val_1061_ = lean_noption_get(v___x_1037_);
v___x_1062_ = l_Lean_ExprStructEq_beq(v_val_1061_, v_query_1020_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
lean_dec(v_val_1061_);
v___x_1063_ = lean_array_get_size(v_keyArray_1035_);
v___x_1064_ = lean_nat_add(v_x_1023_, v_one_1048_);
lean_dec(v_x_1023_);
v___x_1065_ = lean_nat_dec_lt(v___x_1064_, v___x_1063_);
if (v___x_1065_ == 0)
{
lean_dec(v___x_1064_);
v_x_1022_ = v_n_1049_;
v_x_1023_ = v_zero_1024_;
goto _start;
}
else
{
v_x_1022_ = v_n_1049_;
v_x_1023_ = v___x_1064_;
goto _start;
}
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1069_; 
lean_dec(v_n_1049_);
lean_dec(v_x_1021_);
lean_inc(v___x_1059_);
v_val_1068_ = lean_noption_get(v___x_1059_);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v_x_1023_);
lean_ctor_set(v___x_1069_, 1, v_val_1061_);
lean_ctor_set(v___x_1069_, 2, v_val_1068_);
return v___x_1069_;
}
}
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_array_get_size(v_keyArray_1035_);
v___x_1053_ = lean_nat_add(v_x_1023_, v_one_1048_);
lean_dec(v_x_1023_);
v___x_1054_ = lean_nat_dec_lt(v___x_1053_, v___x_1052_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1053_);
v_x_1021_ = v___y_1051_;
v_x_1022_ = v_n_1049_;
v_x_1023_ = v_zero_1024_;
goto _start;
}
else
{
v_x_1021_ = v___y_1051_;
v_x_1022_ = v_n_1049_;
v_x_1023_ = v___x_1053_;
goto _start;
}
}
v___jp_1057_:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v___x_1058_; 
lean_inc(v_x_1023_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_x_1023_);
v___y_1051_ = v___x_1058_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v_x_1021_;
goto v___jp_1050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg___boxed(lean_object* v_m_1070_, lean_object* v_query_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_m_1070_, v_query_1071_, v_x_1072_, v_x_1073_, v_x_1074_);
lean_dec_ref(v_query_1071_);
lean_dec_ref(v_m_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_1076_, lean_object* v_query_1077_){
_start:
{
lean_object* v_keyArray_1078_; lean_object* v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v_fold_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_keyArray_1078_ = lean_ctor_get(v_m_1076_, 1);
v___x_1079_ = lean_array_get_size(v_keyArray_1078_);
v___x_1080_ = l_Lean_ExprStructEq_hash(v_query_1077_);
v___x_1081_ = 32ULL;
v___x_1082_ = lean_uint64_shift_right(v___x_1080_, v___x_1081_);
v_fold_1083_ = lean_uint64_xor(v___x_1080_, v___x_1082_);
v___x_1084_ = 16ULL;
v___x_1085_ = lean_uint64_shift_right(v_fold_1083_, v___x_1084_);
v___x_1086_ = lean_uint64_xor(v_fold_1083_, v___x_1085_);
v___x_1087_ = lean_uint64_to_usize(v___x_1086_);
v___x_1088_ = lean_usize_of_nat(v___x_1079_);
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_sub(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_usize_land(v___x_1087_, v___x_1090_);
v___x_1092_ = lean_usize_to_nat(v___x_1091_);
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_m_1076_, v_query_1077_, v___x_1093_, v___x_1079_, v___x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object* v_m_1095_, lean_object* v_query_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_1095_, v_query_1096_);
lean_dec_ref(v_query_1096_);
lean_dec_ref(v_m_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg(lean_object* v_b_1098_, lean_object* v_acc_1099_, lean_object* v_i_1100_){
_start:
{
lean_object* v___y_1102_; lean_object* v_keyArray_1110_; lean_object* v_valueArray_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_keyArray_1110_ = lean_ctor_get(v_b_1098_, 1);
v_valueArray_1111_ = lean_ctor_get(v_b_1098_, 2);
v___x_1112_ = lean_array_get_size(v_keyArray_1110_);
v___x_1113_ = lean_nat_dec_lt(v_i_1100_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec(v_i_1100_);
return v_acc_1099_;
}
else
{
lean_object* v___x_1114_; uint8_t v_isSome_1115_; 
v___x_1114_ = lean_array_fget_borrowed(v_keyArray_1110_, v_i_1100_);
v_isSome_1115_ = lean_noption_is_some(v___x_1114_);
if (v_isSome_1115_ == 0)
{
goto v___jp_1106_;
}
else
{
lean_object* v___x_1116_; uint8_t v_isSome_1117_; 
v___x_1116_ = lean_array_fget_borrowed(v_valueArray_1111_, v_i_1100_);
v_isSome_1117_ = lean_noption_is_some(v___x_1116_);
if (v_isSome_1117_ == 0)
{
goto v___jp_1106_;
}
else
{
lean_object* v_val_1118_; lean_object* v_val_1119_; lean_object* v_i_1121_; lean_object* v___x_1126_; 
lean_inc(v___x_1114_);
v_val_1118_ = lean_noption_get(v___x_1114_);
lean_inc(v___x_1116_);
v_val_1119_ = lean_noption_get(v___x_1116_);
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_acc_1099_, v_val_1118_);
switch(lean_obj_tag(v___x_1126_))
{
case 0:
{
lean_object* v_index_1127_; lean_object* v_size_1128_; lean_object* v___x_1129_; 
v_index_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_index_1127_);
lean_dec_ref_known(v___x_1126_, 3);
v_size_1128_ = lean_ctor_get(v_acc_1099_, 0);
lean_inc(v_size_1128_);
v___x_1129_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1099_, v_size_1128_, v_index_1127_, v_val_1118_, v_val_1119_);
lean_dec(v_index_1127_);
v___y_1102_ = v___x_1129_;
goto v___jp_1101_;
}
case 1:
{
lean_object* v_index_1130_; 
v_index_1130_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_index_1130_);
lean_dec_ref_known(v___x_1126_, 1);
v_i_1121_ = v_index_1130_;
goto v___jp_1120_;
}
default: 
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1099_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_index_1133_; 
v_index_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_index_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v_i_1121_ = v_index_1133_;
goto v___jp_1120_;
}
else
{
lean_dec(v_val_1119_);
lean_dec(v_val_1118_);
v___y_1102_ = v_acc_1099_;
goto v___jp_1101_;
}
}
}
v___jp_1120_:
{
lean_object* v_size_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_size_1122_ = lean_ctor_get(v_acc_1099_, 0);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_add(v_size_1122_, v___x_1123_);
v___x_1125_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1099_, v___x_1124_, v_i_1121_, v_val_1118_, v_val_1119_);
lean_dec(v_i_1121_);
v___y_1102_ = v___x_1125_;
goto v___jp_1101_;
}
}
}
}
v___jp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v_i_1100_, v___x_1103_);
lean_dec(v_i_1100_);
v_acc_1099_ = v___y_1102_;
v_i_1100_ = v___x_1104_;
goto _start;
}
v___jp_1106_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_i_1100_, v___x_1107_);
lean_dec(v_i_1100_);
v_i_1100_ = v___x_1108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg___boxed(lean_object* v_b_1134_, lean_object* v_acc_1135_, lean_object* v_i_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg(v_b_1134_, v_acc_1135_, v_i_1136_);
lean_dec_ref(v_b_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object* v_init_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg(v_b_1139_, v_init_1138_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg___boxed(lean_object* v_init_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_init_1142_, v_b_1143_);
lean_dec_ref(v_b_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object* v_m_1145_){
_start:
{
lean_object* v_keyArray_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_cellCount_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_target_1153_; lean_object* v___x_1154_; 
v_keyArray_1146_ = lean_ctor_get(v_m_1145_, 1);
v___x_1147_ = lean_array_get_size(v_keyArray_1146_);
v___x_1148_ = lean_unsigned_to_nat(2u);
v_cellCount_1149_ = lean_nat_mul(v___x_1147_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1149_);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1149_);
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1149_);
v_target_1153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1153_, 0, v___x_1150_);
lean_ctor_set(v_target_1153_, 1, v___x_1151_);
lean_ctor_set(v_target_1153_, 2, v___x_1152_);
v___x_1154_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_target_1153_, v_m_1145_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg___boxed(lean_object* v_m_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_1155_);
lean_dec_ref(v_m_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1157_, lean_object* v_e_1158_, lean_object* v_fst_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___y_1164_; lean_object* v___y_1167_; lean_object* v_i_1168_; lean_object* v___y_1184_; lean_object* v_i_1185_; lean_object* v___y_1191_; lean_object* v___x_1200_; 
v___x_1161_ = lean_st_ref_take(v_a_1157_);
v___x_1162_ = lean_box(0);
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1161_, v_e_1158_);
switch(lean_obj_tag(v___x_1200_))
{
case 0:
{
lean_object* v_index_1201_; lean_object* v_size_1202_; lean_object* v___x_1203_; 
v_index_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_index_1201_);
lean_dec_ref_known(v___x_1200_, 3);
v_size_1202_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_size_1202_);
v___x_1203_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1161_, v_size_1202_, v_index_1201_, v_e_1158_, v_fst_1159_);
lean_dec(v_index_1201_);
v___y_1164_ = v___x_1203_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v_index_1204_; lean_object* v_size_1205_; lean_object* v_keyArray_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_index_1204_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_index_1204_);
lean_dec_ref_known(v___x_1200_, 1);
v_size_1205_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_size_1205_);
v_keyArray_1206_ = lean_ctor_get(v___x_1161_, 1);
lean_inc_ref(v_keyArray_1206_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_size_1205_, v___x_1207_);
lean_dec(v_size_1205_);
v___x_1209_ = lean_array_get_size(v_keyArray_1206_);
lean_dec_ref(v_keyArray_1206_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec(v___x_1208_);
lean_dec(v_index_1204_);
goto v___jp_1173_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1211_ = lean_unsigned_to_nat(4u);
v___x_1212_ = lean_nat_mul(v___x_1208_, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(3u);
v___x_1214_ = lean_nat_mul(v___x_1209_, v___x_1213_);
v___x_1215_ = lean_nat_dec_le(v___x_1212_, v___x_1214_);
lean_dec(v___x_1214_);
lean_dec(v___x_1212_);
if (v___x_1215_ == 0)
{
lean_dec(v___x_1208_);
lean_dec(v_index_1204_);
goto v___jp_1173_;
}
else
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1161_, v___x_1208_, v_index_1204_, v_e_1158_, v_fst_1159_);
lean_dec(v_index_1204_);
v___y_1164_ = v___x_1216_;
goto v___jp_1163_;
}
}
}
default: 
{
lean_object* v_size_1217_; lean_object* v_keyArray_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_size_1217_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_size_1217_);
v_keyArray_1218_ = lean_ctor_get(v___x_1161_, 1);
lean_inc_ref(v_keyArray_1218_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_size_1217_, v___x_1219_);
lean_dec(v_size_1217_);
v___x_1221_ = lean_array_get_size(v_keyArray_1218_);
lean_dec_ref(v_keyArray_1218_);
v___x_1222_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec(v___x_1220_);
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1161_);
lean_dec(v___x_1161_);
v___y_1191_ = v___x_1223_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1224_ = lean_unsigned_to_nat(4u);
v___x_1225_ = lean_nat_mul(v___x_1220_, v___x_1224_);
lean_dec(v___x_1220_);
v___x_1226_ = lean_unsigned_to_nat(3u);
v___x_1227_ = lean_nat_mul(v___x_1221_, v___x_1226_);
v___x_1228_ = lean_nat_dec_le(v___x_1225_, v___x_1227_);
lean_dec(v___x_1227_);
lean_dec(v___x_1225_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1161_);
lean_dec(v___x_1161_);
v___y_1191_ = v___x_1229_;
goto v___jp_1190_;
}
else
{
v___y_1191_ = v___x_1161_;
goto v___jp_1190_;
}
}
}
}
v___jp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_st_ref_put(v_a_1157_, v___y_1164_);
return v___x_1162_;
}
v___jp_1166_:
{
lean_object* v_size_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_size_1169_ = lean_ctor_get(v___y_1167_, 0);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_size_1169_, v___x_1170_);
v___x_1172_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1167_, v___x_1171_, v_i_1168_, v_e_1158_, v_fst_1159_);
lean_dec(v_i_1168_);
v___y_1164_ = v___x_1172_;
goto v___jp_1163_;
}
v___jp_1173_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1161_);
lean_dec(v___x_1161_);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1174_, v_e_1158_);
switch(lean_obj_tag(v___x_1175_))
{
case 0:
{
lean_object* v_index_1176_; lean_object* v_size_1177_; lean_object* v___x_1178_; 
v_index_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_index_1176_);
lean_dec_ref_known(v___x_1175_, 3);
v_size_1177_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_size_1177_);
v___x_1178_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1174_, v_size_1177_, v_index_1176_, v_e_1158_, v_fst_1159_);
lean_dec(v_index_1176_);
v___y_1164_ = v___x_1178_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v_index_1179_; 
v_index_1179_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_index_1179_);
lean_dec_ref_known(v___x_1175_, 1);
v___y_1167_ = v___x_1174_;
v_i_1168_ = v_index_1179_;
goto v___jp_1166_;
}
default: 
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1174_, v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_index_1182_; 
v_index_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_index_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___y_1167_ = v___x_1174_;
v_i_1168_ = v_index_1182_;
goto v___jp_1166_;
}
else
{
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v_e_1158_);
v___y_1164_ = v___x_1174_;
goto v___jp_1163_;
}
}
}
}
v___jp_1183_:
{
lean_object* v_size_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_size_1186_ = lean_ctor_get(v___y_1184_, 0);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_size_1186_, v___x_1187_);
v___x_1189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1184_, v___x_1188_, v_i_1185_, v_e_1158_, v_fst_1159_);
lean_dec(v_i_1185_);
v___y_1164_ = v___x_1189_;
goto v___jp_1163_;
}
v___jp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___y_1191_, v_e_1158_);
switch(lean_obj_tag(v___x_1192_))
{
case 0:
{
lean_object* v_index_1193_; lean_object* v_size_1194_; lean_object* v___x_1195_; 
v_index_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_index_1193_);
lean_dec_ref_known(v___x_1192_, 3);
v_size_1194_ = lean_ctor_get(v___y_1191_, 0);
lean_inc(v_size_1194_);
v___x_1195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1191_, v_size_1194_, v_index_1193_, v_e_1158_, v_fst_1159_);
lean_dec(v_index_1193_);
v___y_1164_ = v___x_1195_;
goto v___jp_1163_;
}
case 1:
{
lean_object* v_index_1196_; 
v_index_1196_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_index_1196_);
lean_dec_ref_known(v___x_1192_, 1);
v___y_1184_ = v___y_1191_;
v_i_1185_ = v_index_1196_;
goto v___jp_1183_;
}
default: 
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1191_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_index_1199_; 
v_index_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_index_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___y_1184_ = v___y_1191_;
v_i_1185_ = v_index_1199_;
goto v___jp_1183_;
}
else
{
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v_e_1158_);
v___y_1164_ = v___y_1191_;
goto v___jp_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1230_, lean_object* v_e_1231_, lean_object* v_fst_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1230_, v_e_1231_, v_fst_1232_);
lean_dec(v_a_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg(lean_object* v_m_1235_, lean_object* v_query_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_1235_, v_query_1236_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_index_1238_; lean_object* v_key_1239_; lean_object* v_value_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_index_1238_ = lean_ctor_get(v___x_1237_, 0);
v_key_1239_ = lean_ctor_get(v___x_1237_, 1);
v_value_1240_ = lean_ctor_get(v___x_1237_, 2);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1237_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_value_1240_);
lean_inc(v_key_1239_);
lean_inc(v_index_1238_);
lean_dec(v___x_1237_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_index_1238_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_key_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_value_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; 
lean_dec(v___x_1237_);
v___x_1248_ = lean_box(1);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg___boxed(lean_object* v_m_1249_, lean_object* v_query_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg(v_m_1249_, v_query_1250_);
lean_dec_ref(v_query_1250_);
lean_dec_ref(v_m_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg(v_m_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_value_1255_; lean_object* v___x_1256_; 
v_value_1255_ = lean_ctor_get(v___x_1254_, 2);
lean_inc(v_value_1255_);
lean_dec_ref_known(v___x_1254_, 3);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_value_1255_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1258_, v_a_1259_);
lean_dec_ref(v_a_1259_);
lean_dec_ref(v_m_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_apply_1(v_x_1262_, lean_box(0));
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___y_1263_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1272_, v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1284_, lean_object* v_pre_1285_, lean_object* v_post_1286_, uint8_t v_usedLetOnly_1287_, uint8_t v_skipConstInApp_1288_, uint8_t v_skipInstances_1289_, lean_object* v_body_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_array_push(v_fvars_1284_, v_x_1291_);
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1285_, v_post_1286_, v_usedLetOnly_1287_, v_skipConstInApp_1288_, v_skipInstances_1289_, v___x_1299_, v_body_1290_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1301_, lean_object* v_pre_1302_, lean_object* v_post_1303_, lean_object* v_usedLetOnly_1304_, lean_object* v_skipConstInApp_1305_, lean_object* v_skipInstances_1306_, lean_object* v_body_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_usedLetOnly_boxed_1316_; uint8_t v_skipConstInApp_boxed_1317_; uint8_t v_skipInstances_boxed_1318_; lean_object* v_res_1319_; 
v_usedLetOnly_boxed_1316_ = lean_unbox(v_usedLetOnly_1304_);
v_skipConstInApp_boxed_1317_ = lean_unbox(v_skipConstInApp_1305_);
v_skipInstances_boxed_1318_ = lean_unbox(v_skipInstances_1306_);
v_res_1319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1301_, v_pre_1302_, v_post_1303_, v_usedLetOnly_boxed_1316_, v_skipConstInApp_boxed_1317_, v_skipInstances_boxed_1318_, v_body_1307_, v_x_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1309_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1320_, lean_object* v_post_1321_, uint8_t v_usedLetOnly_1322_, uint8_t v_skipConstInApp_1323_, uint8_t v_skipInstances_1324_, lean_object* v_e_1325_, lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
lean_inc_ref(v_post_1321_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc_ref(v_e_1325_);
v___x_1333_ = lean_apply_7(v_post_1321_, v_e_1325_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, lean_box(0));
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1365_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1365_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1365_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1364_; 
v_fst_1338_ = lean_ctor_get(v_a_1334_, 0);
v_snd_1339_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1341_ = v_a_1334_;
v_isShared_1342_ = v_isSharedCheck_1364_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_inc(v_fst_1338_);
lean_dec(v_a_1334_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1364_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___y_1344_; 
switch(lean_obj_tag(v_fst_1338_))
{
case 0:
{
lean_object* v_e_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
lean_del_object(v___x_1341_);
lean_del_object(v___x_1336_);
lean_dec_ref(v_e_1325_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
v_e_1351_ = lean_ctor_get(v_fst_1338_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_fst_1338_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1353_ = v_fst_1338_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_e_1351_);
lean_dec(v_fst_1338_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_e_1351_);
lean_ctor_set(v___x_1355_, 1, v_snd_1339_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
case 1:
{
lean_object* v_e_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1341_);
lean_del_object(v___x_1336_);
lean_dec_ref(v_e_1325_);
v_e_1360_ = lean_ctor_get(v_fst_1338_, 0);
lean_inc_ref(v_e_1360_);
lean_dec_ref_known(v_fst_1338_, 1);
v___x_1361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1320_, v_post_1321_, v_usedLetOnly_1322_, v_skipConstInApp_1323_, v_skipInstances_1324_, v_e_1360_, v_a_1326_, v_snd_1339_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1361_;
}
default: 
{
lean_object* v_e_x3f_1362_; 
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
v_e_x3f_1362_ = lean_ctor_get(v_fst_1338_, 0);
lean_inc(v_e_x3f_1362_);
lean_dec_ref_known(v_fst_1338_, 1);
if (lean_obj_tag(v_e_x3f_1362_) == 0)
{
v___y_1344_ = v_e_1325_;
goto v___jp_1343_;
}
else
{
lean_object* v_val_1363_; 
lean_dec_ref(v_e_1325_);
v_val_1363_ = lean_ctor_get(v_e_x3f_1362_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v_e_x3f_1362_, 1);
v___y_1344_ = v_val_1363_;
goto v___jp_1343_;
}
}
}
v___jp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___y_1344_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___y_1344_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1339_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1346_);
v___x_1348_ = v___x_1336_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v_e_1325_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
v_a_1366_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1333_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1333_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1374_, lean_object* v_post_1375_, uint8_t v_usedLetOnly_1376_, uint8_t v_skipConstInApp_1377_, uint8_t v_skipInstances_1378_, lean_object* v_fvars_1379_, lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
if (lean_obj_tag(v_e_1380_) == 6)
{
lean_object* v_binderName_1388_; lean_object* v_binderType_1389_; lean_object* v_body_1390_; uint8_t v_binderInfo_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_binderName_1388_ = lean_ctor_get(v_e_1380_, 0);
lean_inc(v_binderName_1388_);
v_binderType_1389_ = lean_ctor_get(v_e_1380_, 1);
lean_inc_ref(v_binderType_1389_);
v_body_1390_ = lean_ctor_get(v_e_1380_, 2);
lean_inc_ref(v_body_1390_);
v_binderInfo_1391_ = lean_ctor_get_uint8(v_e_1380_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1380_, 3);
v___x_1392_ = lean_expr_instantiate_rev(v_binderType_1389_, v_fvars_1379_);
lean_dec_ref(v_binderType_1389_);
lean_inc_ref(v_post_1375_);
lean_inc_ref(v_pre_1374_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1374_, v_post_1375_, v_usedLetOnly_1376_, v_skipConstInApp_1377_, v_skipInstances_1378_, v___x_1392_, v_a_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_fst_1395_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_fst_1395_);
v_snd_1396_ = lean_ctor_get(v_a_1394_, 1);
lean_inc(v_snd_1396_);
lean_dec(v_a_1394_);
v___x_1397_ = lean_box(v_usedLetOnly_1376_);
v___x_1398_ = lean_box(v_skipConstInApp_1377_);
v___x_1399_ = lean_box(v_skipInstances_1378_);
v___f_1400_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1400_, 0, v_fvars_1379_);
lean_closure_set(v___f_1400_, 1, v_pre_1374_);
lean_closure_set(v___f_1400_, 2, v_post_1375_);
lean_closure_set(v___f_1400_, 3, v___x_1397_);
lean_closure_set(v___f_1400_, 4, v___x_1398_);
lean_closure_set(v___f_1400_, 5, v___x_1399_);
lean_closure_set(v___f_1400_, 6, v_body_1390_);
v___x_1401_ = 0;
v___x_1402_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(v_binderName_1388_, v_binderInfo_1391_, v_fst_1395_, v___f_1400_, v___x_1401_, v_a_1381_, v_snd_1396_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1402_;
}
else
{
lean_dec_ref(v_body_1390_);
lean_dec(v_binderName_1388_);
lean_dec_ref(v_fvars_1379_);
lean_dec_ref(v_post_1375_);
lean_dec_ref(v_pre_1374_);
return v___x_1393_;
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_expr_instantiate_rev(v_e_1380_, v_fvars_1379_);
lean_dec_ref(v_e_1380_);
lean_inc_ref(v_post_1375_);
lean_inc_ref(v_pre_1374_);
v___x_1404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1374_, v_post_1375_, v_usedLetOnly_1376_, v_skipConstInApp_1377_, v_skipInstances_1378_, v___x_1403_, v_a_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v_fst_1406_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_a_1405_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_a_1405_);
v___x_1408_ = 0;
v___x_1409_ = 1;
v___x_1410_ = 1;
v___x_1411_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1379_, v_fst_1406_, v___x_1408_, v_usedLetOnly_1376_, v___x_1408_, v___x_1409_, v___x_1410_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec_ref(v_fvars_1379_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1374_, v_post_1375_, v_usedLetOnly_1376_, v_skipConstInApp_1377_, v_skipInstances_1378_, v_a_1412_, v_a_1381_, v_snd_1407_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1413_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_snd_1407_);
lean_dec_ref(v_post_1375_);
lean_dec_ref(v_pre_1374_);
v_a_1414_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1411_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1411_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1379_);
lean_dec_ref(v_post_1375_);
lean_dec_ref(v_pre_1374_);
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1422_, lean_object* v_pre_1423_, lean_object* v_post_1424_, uint8_t v_usedLetOnly_1425_, uint8_t v_skipConstInApp_1426_, uint8_t v_skipInstances_1427_, lean_object* v_body_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_array_push(v_fvars_1422_, v_x_1429_);
v___x_1438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1423_, v_post_1424_, v_usedLetOnly_1425_, v_skipConstInApp_1426_, v_skipInstances_1427_, v___x_1437_, v_body_1428_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1439_, lean_object* v_pre_1440_, lean_object* v_post_1441_, lean_object* v_usedLetOnly_1442_, lean_object* v_skipConstInApp_1443_, lean_object* v_skipInstances_1444_, lean_object* v_body_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_usedLetOnly_boxed_1454_; uint8_t v_skipConstInApp_boxed_1455_; uint8_t v_skipInstances_boxed_1456_; lean_object* v_res_1457_; 
v_usedLetOnly_boxed_1454_ = lean_unbox(v_usedLetOnly_1442_);
v_skipConstInApp_boxed_1455_ = lean_unbox(v_skipConstInApp_1443_);
v_skipInstances_boxed_1456_ = lean_unbox(v_skipInstances_1444_);
v_res_1457_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1439_, v_pre_1440_, v_post_1441_, v_usedLetOnly_boxed_1454_, v_skipConstInApp_boxed_1455_, v_skipInstances_boxed_1456_, v_body_1445_, v_x_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1447_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1458_, lean_object* v_post_1459_, uint8_t v_usedLetOnly_1460_, uint8_t v_skipConstInApp_1461_, uint8_t v_skipInstances_1462_, lean_object* v_fvars_1463_, lean_object* v_e_1464_, lean_object* v_a_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
if (lean_obj_tag(v_e_1464_) == 8)
{
lean_object* v_declName_1472_; lean_object* v_type_1473_; lean_object* v_value_1474_; lean_object* v_body_1475_; uint8_t v_nondep_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_declName_1472_ = lean_ctor_get(v_e_1464_, 0);
lean_inc(v_declName_1472_);
v_type_1473_ = lean_ctor_get(v_e_1464_, 1);
lean_inc_ref(v_type_1473_);
v_value_1474_ = lean_ctor_get(v_e_1464_, 2);
lean_inc_ref(v_value_1474_);
v_body_1475_ = lean_ctor_get(v_e_1464_, 3);
lean_inc_ref(v_body_1475_);
v_nondep_1476_ = lean_ctor_get_uint8(v_e_1464_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1464_, 4);
v___x_1477_ = lean_expr_instantiate_rev(v_type_1473_, v_fvars_1463_);
lean_dec_ref(v_type_1473_);
lean_inc_ref(v_post_1459_);
lean_inc_ref(v_pre_1458_);
v___x_1478_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1458_, v_post_1459_, v_usedLetOnly_1460_, v_skipConstInApp_1461_, v_skipInstances_1462_, v___x_1477_, v_a_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v_fst_1480_ = lean_ctor_get(v_a_1479_, 0);
lean_inc(v_fst_1480_);
v_snd_1481_ = lean_ctor_get(v_a_1479_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_a_1479_);
v___x_1482_ = lean_expr_instantiate_rev(v_value_1474_, v_fvars_1463_);
lean_dec_ref(v_value_1474_);
lean_inc_ref(v_post_1459_);
lean_inc_ref(v_pre_1458_);
v___x_1483_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1458_, v_post_1459_, v_usedLetOnly_1460_, v_skipConstInApp_1461_, v_skipInstances_1462_, v___x_1482_, v_a_1465_, v_snd_1481_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___f_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v_fst_1485_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_fst_1485_);
v_snd_1486_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_snd_1486_);
lean_dec(v_a_1484_);
v___x_1487_ = lean_box(v_usedLetOnly_1460_);
v___x_1488_ = lean_box(v_skipConstInApp_1461_);
v___x_1489_ = lean_box(v_skipInstances_1462_);
v___f_1490_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1490_, 0, v_fvars_1463_);
lean_closure_set(v___f_1490_, 1, v_pre_1458_);
lean_closure_set(v___f_1490_, 2, v_post_1459_);
lean_closure_set(v___f_1490_, 3, v___x_1487_);
lean_closure_set(v___f_1490_, 4, v___x_1488_);
lean_closure_set(v___f_1490_, 5, v___x_1489_);
lean_closure_set(v___f_1490_, 6, v_body_1475_);
v___x_1491_ = 0;
v___x_1492_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg(v_declName_1472_, v_fst_1480_, v_fst_1485_, v___f_1490_, v_nondep_1476_, v___x_1491_, v_a_1465_, v_snd_1486_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1492_;
}
else
{
lean_dec(v_fst_1480_);
lean_dec_ref(v_body_1475_);
lean_dec(v_declName_1472_);
lean_dec_ref(v_fvars_1463_);
lean_dec_ref(v_post_1459_);
lean_dec_ref(v_pre_1458_);
return v___x_1483_;
}
}
else
{
lean_dec_ref(v_body_1475_);
lean_dec_ref(v_value_1474_);
lean_dec(v_declName_1472_);
lean_dec_ref(v_fvars_1463_);
lean_dec_ref(v_post_1459_);
lean_dec_ref(v_pre_1458_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_expr_instantiate_rev(v_e_1464_, v_fvars_1463_);
lean_dec_ref(v_e_1464_);
lean_inc_ref(v_post_1459_);
lean_inc_ref(v_pre_1458_);
v___x_1494_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1458_, v_post_1459_, v_usedLetOnly_1460_, v_skipConstInApp_1461_, v_skipInstances_1462_, v___x_1493_, v_a_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; uint8_t v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v_fst_1496_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v_a_1495_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_a_1495_);
v___x_1498_ = 0;
v___x_1499_ = 1;
v___x_1500_ = l_Lean_Meta_mkLetFVars(v_fvars_1463_, v_fst_1496_, v_usedLetOnly_1460_, v___x_1498_, v___x_1499_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec_ref(v_fvars_1463_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1458_, v_post_1459_, v_usedLetOnly_1460_, v_skipConstInApp_1461_, v_skipInstances_1462_, v_a_1501_, v_a_1465_, v_snd_1497_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1502_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_snd_1497_);
lean_dec_ref(v_post_1459_);
lean_dec_ref(v_pre_1458_);
v_a_1503_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1500_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1500_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1463_);
lean_dec_ref(v_post_1459_);
lean_dec_ref(v_pre_1458_);
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1511_, lean_object* v_post_1512_, uint8_t v_usedLetOnly_1513_, uint8_t v_skipConstInApp_1514_, uint8_t v_skipInstances_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_bs_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v_post_1512_);
lean_dec_ref(v_pre_1511_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_bs_1518_);
lean_ctor_set(v___x_1527_, 1, v___y_1520_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v_v_1529_; lean_object* v___x_1530_; 
v_v_1529_ = lean_array_uget_borrowed(v_bs_1518_, v_i_1517_);
lean_inc(v_v_1529_);
lean_inc_ref(v_post_1512_);
lean_inc_ref(v_pre_1511_);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1511_, v_post_1512_, v_usedLetOnly_1513_, v_skipConstInApp_1514_, v_skipInstances_1515_, v_v_1529_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v_fst_1532_; lean_object* v_snd_1533_; lean_object* v___x_1534_; lean_object* v_bs_x27_1535_; size_t v___x_1536_; size_t v___x_1537_; lean_object* v___x_1538_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_fst_1532_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_fst_1532_);
v_snd_1533_ = lean_ctor_get(v_a_1531_, 1);
lean_inc(v_snd_1533_);
lean_dec(v_a_1531_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v_bs_x27_1535_ = lean_array_uset(v_bs_1518_, v_i_1517_, v___x_1534_);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1517_, v___x_1536_);
v___x_1538_ = lean_array_uset(v_bs_x27_1535_, v_i_1517_, v_fst_1532_);
v_i_1517_ = v___x_1537_;
v_bs_1518_ = v___x_1538_;
v___y_1520_ = v_snd_1533_;
goto _start;
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref(v_bs_1518_);
lean_dec_ref(v_post_1512_);
lean_dec_ref(v_pre_1511_);
v_a_1540_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1530_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1530_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1548_, lean_object* v_post_1549_, uint8_t v_usedLetOnly_1550_, uint8_t v_skipConstInApp_1551_, uint8_t v_skipInstances_1552_, lean_object* v___x_1553_, lean_object* v___y_1554_, lean_object* v_b_1555_, lean_object* v_a_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1548_, v_post_1549_, v_usedLetOnly_1550_, v_skipConstInApp_1551_, v_skipInstances_1552_, v___x_1553_, v___y_1554_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1582_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1581_; 
v_fst_1568_ = lean_ctor_get(v_a_1564_, 0);
v_snd_1569_ = lean_ctor_get(v_a_1564_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1571_ = v_a_1564_;
v_isShared_1572_ = v_isSharedCheck_1581_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_inc(v_fst_1568_);
lean_dec(v_a_1564_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1581_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_array_fset(v_b_1555_, v_a_1556_, v_fst_1568_);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1569_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1576_);
v___x_1578_ = v___x_1566_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_b_1555_);
v_a_1583_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1563_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1563_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1591_, lean_object* v_post_1592_, lean_object* v_usedLetOnly_1593_, lean_object* v_skipConstInApp_1594_, lean_object* v_skipInstances_1595_, lean_object* v___x_1596_, lean_object* v___y_1597_, lean_object* v_b_1598_, lean_object* v_a_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v_usedLetOnly_boxed_1606_; uint8_t v_skipConstInApp_boxed_1607_; uint8_t v_skipInstances_boxed_1608_; lean_object* v_res_1609_; 
v_usedLetOnly_boxed_1606_ = lean_unbox(v_usedLetOnly_1593_);
v_skipConstInApp_boxed_1607_ = lean_unbox(v_skipConstInApp_1594_);
v_skipInstances_boxed_1608_ = lean_unbox(v_skipInstances_1595_);
v_res_1609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1591_, v_post_1592_, v_usedLetOnly_boxed_1606_, v_skipConstInApp_boxed_1607_, v_skipInstances_boxed_1608_, v___x_1596_, v___y_1597_, v_b_1598_, v_a_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_a_1599_);
lean_dec(v___y_1597_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1610_, lean_object* v___x_1611_, lean_object* v_pre_1612_, lean_object* v_post_1613_, uint8_t v_usedLetOnly_1614_, uint8_t v_skipConstInApp_1615_, uint8_t v_skipInstances_1616_, lean_object* v_a_1617_, lean_object* v_b_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___y_1627_; uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_lt(v_a_1617_, v_upperBound_1610_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v_a_1617_);
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v_b_1618_);
lean_ctor_set(v___x_1662_, 1, v___y_1620_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1664_ = lean_array_fget_borrowed(v_b_1618_, v_a_1617_);
v___x_1665_ = lean_array_get_size(v___x_1611_);
v___x_1666_ = lean_nat_dec_lt(v_a_1617_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; 
lean_inc(v___x_1664_);
v___x_1667_ = lean_box(v_usedLetOnly_1614_);
v___x_1668_ = lean_box(v_skipConstInApp_1615_);
v___x_1669_ = lean_box(v_skipInstances_1616_);
lean_inc(v_a_1617_);
lean_inc(v___y_1619_);
lean_inc_ref(v_post_1613_);
lean_inc_ref(v_pre_1612_);
v___f_1670_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1670_, 0, v_pre_1612_);
lean_closure_set(v___f_1670_, 1, v_post_1613_);
lean_closure_set(v___f_1670_, 2, v___x_1667_);
lean_closure_set(v___f_1670_, 3, v___x_1668_);
lean_closure_set(v___f_1670_, 4, v___x_1669_);
lean_closure_set(v___f_1670_, 5, v___x_1664_);
lean_closure_set(v___f_1670_, 6, v___y_1619_);
lean_closure_set(v___f_1670_, 7, v_b_1618_);
lean_closure_set(v___f_1670_, 8, v_a_1617_);
v___y_1627_ = v___f_1670_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1671_; uint8_t v_isInstance_1672_; 
v___x_1671_ = lean_array_fget_borrowed(v___x_1611_, v_a_1617_);
v_isInstance_1672_ = lean_ctor_get_uint8(v___x_1671_, sizeof(void*)*1 + 4);
if (v_isInstance_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___f_1676_; 
lean_inc(v___x_1664_);
v___x_1673_ = lean_box(v_usedLetOnly_1614_);
v___x_1674_ = lean_box(v_skipConstInApp_1615_);
v___x_1675_ = lean_box(v_skipInstances_1616_);
lean_inc(v_a_1617_);
lean_inc(v___y_1619_);
lean_inc_ref(v_post_1613_);
lean_inc_ref(v_pre_1612_);
v___f_1676_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1676_, 0, v_pre_1612_);
lean_closure_set(v___f_1676_, 1, v_post_1613_);
lean_closure_set(v___f_1676_, 2, v___x_1673_);
lean_closure_set(v___f_1676_, 3, v___x_1674_);
lean_closure_set(v___f_1676_, 4, v___x_1675_);
lean_closure_set(v___f_1676_, 5, v___x_1664_);
lean_closure_set(v___f_1676_, 6, v___y_1619_);
lean_closure_set(v___f_1676_, 7, v_b_1618_);
lean_closure_set(v___f_1676_, 8, v_a_1617_);
v___y_1627_ = v___f_1676_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1677_; lean_object* v___f_1678_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_b_1618_);
v___f_1678_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1678_, 0, v___x_1677_);
v___y_1627_ = v___f_1678_;
goto v___jp_1626_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; 
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
v___x_1628_ = lean_apply_6(v___y_1627_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1652_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_fst_1633_; 
v_fst_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_fst_1633_);
if (lean_obj_tag(v_fst_1633_) == 0)
{
lean_object* v_snd_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_a_1617_);
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
v_snd_1634_ = lean_ctor_get(v_a_1629_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_a_1629_, 0);
lean_dec(v_unused_1646_);
v___x_1636_ = v_a_1629_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_snd_1634_);
lean_dec(v_a_1629_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_a_1638_; lean_object* v___x_1640_; 
v_a_1638_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v_fst_1633_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_a_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_snd_1634_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1640_);
v___x_1642_ = v___x_1631_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_snd_1647_; lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_del_object(v___x_1631_);
v_snd_1647_ = lean_ctor_get(v_a_1629_, 1);
lean_inc(v_snd_1647_);
lean_dec(v_a_1629_);
v_a_1648_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v_fst_1633_, 1);
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = lean_nat_add(v_a_1617_, v___x_1649_);
lean_dec(v_a_1617_);
v_a_1617_ = v___x_1650_;
v_b_1618_ = v_a_1648_;
v___y_1620_ = v_snd_1647_;
goto _start;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1617_);
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
v_a_1653_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1628_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1628_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1679_, lean_object* v_pre_1680_, lean_object* v_post_1681_, uint8_t v_usedLetOnly_1682_, uint8_t v_skipConstInApp_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_f_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; 
if (lean_obj_tag(v_x_1684_) == 5)
{
lean_object* v_fn_1750_; lean_object* v_arg_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_fn_1750_ = lean_ctor_get(v_x_1684_, 0);
lean_inc_ref(v_fn_1750_);
v_arg_1751_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_arg_1751_);
lean_dec_ref_known(v_x_1684_, 2);
v___x_1752_ = lean_array_set(v_x_1685_, v_x_1686_, v_arg_1751_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_sub(v_x_1686_, v___x_1753_);
lean_dec(v_x_1686_);
v_x_1684_ = v_fn_1750_;
v_x_1685_ = v___x_1752_;
v_x_1686_ = v___x_1754_;
goto _start;
}
else
{
lean_dec(v_x_1686_);
if (v_skipConstInApp_1683_ == 0)
{
goto v___jp_1745_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = l_Lean_Expr_isConst(v_x_1684_);
if (v___x_1756_ == 0)
{
goto v___jp_1745_;
}
else
{
v_f_1695_ = v_x_1684_;
v___y_1696_ = v___y_1687_;
v___y_1697_ = v___y_1688_;
v___y_1698_ = v___y_1689_;
v___y_1699_ = v___y_1690_;
v___y_1700_ = v___y_1691_;
v___y_1701_ = v___y_1692_;
goto v___jp_1694_;
}
}
}
v___jp_1694_:
{
if (v_skipInstances_1679_ == 0)
{
size_t v_sz_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v_sz_1702_ = lean_array_size(v_x_1685_);
v___x_1703_ = ((size_t)0ULL);
lean_inc_ref(v_post_1681_);
lean_inc_ref(v_pre_1680_);
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1680_, v_post_1681_, v_usedLetOnly_1682_, v_skipConstInApp_1683_, v_skipInstances_1679_, v_sz_1702_, v___x_1703_, v_x_1685_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v_fst_1706_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_fst_1706_);
v_snd_1707_ = lean_ctor_get(v_a_1705_, 1);
lean_inc(v_snd_1707_);
lean_dec(v_a_1705_);
v___x_1708_ = l_Lean_mkAppN(v_f_1695_, v_fst_1706_);
lean_dec(v_fst_1706_);
v___x_1709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1680_, v_post_1681_, v_usedLetOnly_1682_, v_skipConstInApp_1683_, v_skipInstances_1679_, v___x_1708_, v___y_1696_, v_snd_1707_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1709_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_f_1695_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v_a_1710_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1704_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1704_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_x_1685_);
lean_inc_ref(v_f_1695_);
v___x_1719_ = l_Lean_Meta_getFunInfoNArgs(v_f_1695_, v___x_1718_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v_paramInfo_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v_paramInfo_1721_ = lean_ctor_get(v_a_1720_, 0);
lean_inc_ref(v_paramInfo_1721_);
lean_dec(v_a_1720_);
v___x_1722_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1681_);
lean_inc_ref(v_pre_1680_);
v___x_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1718_, v_paramInfo_1721_, v_pre_1680_, v_post_1681_, v_usedLetOnly_1682_, v_skipConstInApp_1683_, v_skipInstances_1679_, v___x_1722_, v_x_1685_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec_ref(v_paramInfo_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v_fst_1725_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_fst_1725_);
v_snd_1726_ = lean_ctor_get(v_a_1724_, 1);
lean_inc(v_snd_1726_);
lean_dec(v_a_1724_);
v___x_1727_ = l_Lean_mkAppN(v_f_1695_, v_fst_1725_);
lean_dec(v_fst_1725_);
v___x_1728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1680_, v_post_1681_, v_usedLetOnly_1682_, v_skipConstInApp_1683_, v_skipInstances_1679_, v___x_1727_, v___y_1696_, v_snd_1726_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1728_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_f_1695_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v_a_1729_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1723_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1723_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v___y_1697_);
lean_dec_ref(v_f_1695_);
lean_dec_ref(v_x_1685_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
v_a_1737_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1719_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1719_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
v___jp_1745_:
{
lean_object* v___x_1746_; 
lean_inc_ref(v_post_1681_);
lean_inc_ref(v_pre_1680_);
v___x_1746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1680_, v_post_1681_, v_usedLetOnly_1682_, v_skipConstInApp_1683_, v_skipInstances_1679_, v_x_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_fst_1748_; lean_object* v_snd_1749_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v_fst_1748_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_fst_1748_);
v_snd_1749_ = lean_ctor_get(v_a_1747_, 1);
lean_inc(v_snd_1749_);
lean_dec(v_a_1747_);
v_f_1695_ = v_fst_1748_;
v___y_1696_ = v___y_1687_;
v___y_1697_ = v_snd_1749_;
v___y_1698_ = v___y_1689_;
v___y_1699_ = v___y_1690_;
v___y_1700_ = v___y_1691_;
v___y_1701_ = v___y_1692_;
goto v___jp_1694_;
}
else
{
lean_dec_ref(v_x_1685_);
lean_dec_ref(v_post_1681_);
lean_dec_ref(v_pre_1680_);
return v___x_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1757_, lean_object* v_pre_1758_, lean_object* v_e_1759_, lean_object* v_post_1760_, uint8_t v_usedLetOnly_1761_, uint8_t v_skipConstInApp_1762_, uint8_t v_skipInstances_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Core_checkSystem(v___x_1757_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref_known(v___x_1771_, 1);
lean_inc_ref(v_pre_1758_);
lean_inc(v___y_1769_);
lean_inc_ref(v___y_1768_);
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc_ref(v_e_1759_);
v___x_1772_ = lean_apply_7(v_pre_1758_, v_e_1759_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, lean_box(0));
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1834_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1834_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1834_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1833_; 
v_fst_1777_ = lean_ctor_get(v_a_1773_, 0);
v_snd_1778_ = lean_ctor_get(v_a_1773_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1780_ = v_a_1773_;
v_isShared_1781_ = v_isSharedCheck_1833_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_inc(v_fst_1777_);
lean_dec(v_a_1773_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1833_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___y_1783_; 
switch(lean_obj_tag(v_fst_1777_))
{
case 0:
{
lean_object* v_e_1822_; lean_object* v___x_1824_; 
lean_dec_ref(v_post_1760_);
lean_dec_ref(v_e_1759_);
lean_dec_ref(v_pre_1758_);
v_e_1822_ = lean_ctor_get(v_fst_1777_, 0);
lean_inc_ref(v_e_1822_);
lean_dec_ref_known(v_fst_1777_, 1);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_e_1822_);
v___x_1824_ = v___x_1780_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_e_1822_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_snd_1778_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1824_);
v___x_1826_ = v___x_1775_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
case 1:
{
lean_object* v_e_1829_; lean_object* v___x_1830_; 
lean_del_object(v___x_1780_);
lean_del_object(v___x_1775_);
lean_dec_ref(v_e_1759_);
v_e_1829_ = lean_ctor_get(v_fst_1777_, 0);
lean_inc_ref(v_e_1829_);
lean_dec_ref_known(v_fst_1777_, 1);
v___x_1830_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v_e_1829_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1830_;
}
default: 
{
lean_object* v_e_x3f_1831_; 
lean_del_object(v___x_1780_);
lean_del_object(v___x_1775_);
v_e_x3f_1831_ = lean_ctor_get(v_fst_1777_, 0);
lean_inc(v_e_x3f_1831_);
lean_dec_ref_known(v_fst_1777_, 1);
if (lean_obj_tag(v_e_x3f_1831_) == 0)
{
v___y_1783_ = v_e_1759_;
goto v___jp_1782_;
}
else
{
lean_object* v_val_1832_; 
lean_dec_ref(v_e_1759_);
v_val_1832_ = lean_ctor_get(v_e_x3f_1831_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v_e_x3f_1831_, 1);
v___y_1783_ = v_val_1832_;
goto v___jp_1782_;
}
}
}
v___jp_1782_:
{
switch(lean_obj_tag(v___y_1783_))
{
case 7:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1785_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1784_, v___y_1783_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1785_;
}
case 6:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1787_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1786_, v___y_1783_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1787_;
}
case 8:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1788_, v___y_1783_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1789_;
}
case 5:
{
lean_object* v_dummy_1790_; lean_object* v_nargs_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_dummy_1790_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1791_ = l_Lean_Expr_getAppNumArgs(v___y_1783_);
lean_inc(v_nargs_1791_);
v___x_1792_ = lean_mk_array(v_nargs_1791_, v_dummy_1790_);
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_nat_sub(v_nargs_1791_, v___x_1793_);
lean_dec(v_nargs_1791_);
v___x_1795_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1763_, v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v___y_1783_, v___x_1792_, v___x_1794_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1795_;
}
case 10:
{
lean_object* v_data_1796_; lean_object* v_expr_1797_; lean_object* v___x_1798_; 
v_data_1796_ = lean_ctor_get(v___y_1783_, 0);
v_expr_1797_ = lean_ctor_get(v___y_1783_, 1);
lean_inc_ref(v_expr_1797_);
lean_inc_ref(v_post_1760_);
lean_inc_ref(v_pre_1758_);
v___x_1798_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v_expr_1797_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; size_t v___x_1802_; size_t v___x_1803_; uint8_t v___x_1804_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v_fst_1800_ = lean_ctor_get(v_a_1799_, 0);
lean_inc(v_fst_1800_);
v_snd_1801_ = lean_ctor_get(v_a_1799_, 1);
lean_inc(v_snd_1801_);
lean_dec(v_a_1799_);
v___x_1802_ = lean_ptr_addr(v_expr_1797_);
v___x_1803_ = lean_ptr_addr(v_fst_1800_);
v___x_1804_ = lean_usize_dec_eq(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_inc(v_data_1796_);
lean_dec_ref_known(v___y_1783_, 2);
v___x_1805_ = l_Lean_Expr_mdata___override(v_data_1796_, v_fst_1800_);
v___x_1806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1805_, v___y_1764_, v_snd_1801_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_fst_1800_);
v___x_1807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___y_1783_, v___y_1764_, v_snd_1801_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1807_;
}
}
else
{
lean_dec_ref_known(v___y_1783_, 2);
lean_dec_ref(v_post_1760_);
lean_dec_ref(v_pre_1758_);
return v___x_1798_;
}
}
case 11:
{
lean_object* v_typeName_1808_; lean_object* v_idx_1809_; lean_object* v_struct_1810_; lean_object* v___x_1811_; 
v_typeName_1808_ = lean_ctor_get(v___y_1783_, 0);
v_idx_1809_ = lean_ctor_get(v___y_1783_, 1);
v_struct_1810_ = lean_ctor_get(v___y_1783_, 2);
lean_inc_ref(v_struct_1810_);
lean_inc_ref(v_post_1760_);
lean_inc_ref(v_pre_1758_);
v___x_1811_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v_struct_1810_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v_fst_1813_; lean_object* v_snd_1814_; size_t v___x_1815_; size_t v___x_1816_; uint8_t v___x_1817_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v_fst_1813_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_fst_1813_);
v_snd_1814_ = lean_ctor_get(v_a_1812_, 1);
lean_inc(v_snd_1814_);
lean_dec(v_a_1812_);
v___x_1815_ = lean_ptr_addr(v_struct_1810_);
v___x_1816_ = lean_ptr_addr(v_fst_1813_);
v___x_1817_ = lean_usize_dec_eq(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc(v_idx_1809_);
lean_inc(v_typeName_1808_);
lean_dec_ref_known(v___y_1783_, 3);
v___x_1818_ = l_Lean_Expr_proj___override(v_typeName_1808_, v_idx_1809_, v_fst_1813_);
v___x_1819_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1818_, v___y_1764_, v_snd_1814_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v_fst_1813_);
v___x_1820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___y_1783_, v___y_1764_, v_snd_1814_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1820_;
}
}
else
{
lean_dec_ref_known(v___y_1783_, 3);
lean_dec_ref(v_post_1760_);
lean_dec_ref(v_pre_1758_);
return v___x_1811_;
}
}
default: 
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1758_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___y_1783_, v___y_1764_, v_snd_1778_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1821_;
}
}
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_post_1760_);
lean_dec_ref(v_e_1759_);
lean_dec_ref(v_pre_1758_);
v_a_1835_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1772_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1772_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v___y_1765_);
lean_dec_ref(v_post_1760_);
lean_dec_ref(v_e_1759_);
lean_dec_ref(v_pre_1758_);
v_a_1843_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1771_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1771_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1851_, lean_object* v_pre_1852_, lean_object* v_e_1853_, lean_object* v_post_1854_, lean_object* v_usedLetOnly_1855_, lean_object* v_skipConstInApp_1856_, lean_object* v_skipInstances_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_usedLetOnly_boxed_1865_; uint8_t v_skipConstInApp_boxed_1866_; uint8_t v_skipInstances_boxed_1867_; lean_object* v_res_1868_; 
v_usedLetOnly_boxed_1865_ = lean_unbox(v_usedLetOnly_1855_);
v_skipConstInApp_boxed_1866_ = lean_unbox(v_skipConstInApp_1856_);
v_skipInstances_boxed_1867_ = lean_unbox(v_skipInstances_1857_);
v_res_1868_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1851_, v_pre_1852_, v_e_1853_, v_post_1854_, v_usedLetOnly_boxed_1865_, v_skipConstInApp_boxed_1866_, v_skipInstances_boxed_1867_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1858_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1869_, lean_object* v_post_1870_, uint8_t v_usedLetOnly_1871_, uint8_t v_skipConstInApp_1872_, uint8_t v_skipInstances_1873_, lean_object* v_e_1874_, lean_object* v_a_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_inc(v_a_1875_);
v___x_1882_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1882_, 0, lean_box(0));
lean_closure_set(v___x_1882_, 1, lean_box(0));
lean_closure_set(v___x_1882_, 2, v_a_1875_);
v___x_1883_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1882_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1938_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1938_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1938_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1937_; 
v_fst_1888_ = lean_ctor_get(v_a_1884_, 0);
v_snd_1889_ = lean_ctor_get(v_a_1884_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1891_ = v_a_1884_;
v_isShared_1892_ = v_isSharedCheck_1937_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v_a_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1937_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1888_, v_e_1874_);
lean_dec(v_fst_1888_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
lean_del_object(v___x_1891_);
lean_del_object(v___x_1886_);
v___x_1894_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1895_ = lean_box(v_usedLetOnly_1871_);
v___x_1896_ = lean_box(v_skipConstInApp_1872_);
v___x_1897_ = lean_box(v_skipInstances_1873_);
lean_inc_ref(v_e_1874_);
v___f_1898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1898_, 0, v___x_1894_);
lean_closure_set(v___f_1898_, 1, v_pre_1869_);
lean_closure_set(v___f_1898_, 2, v_e_1874_);
lean_closure_set(v___f_1898_, 3, v_post_1870_);
lean_closure_set(v___f_1898_, 4, v___x_1895_);
lean_closure_set(v___f_1898_, 5, v___x_1896_);
lean_closure_set(v___f_1898_, 6, v___x_1897_);
v___x_1899_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1898_, v_a_1875_, v_snd_1889_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v_fst_1901_; lean_object* v_snd_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v_fst_1901_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_n(v_fst_1901_, 2);
v_snd_1902_ = lean_ctor_get(v_a_1900_, 1);
lean_inc(v_snd_1902_);
lean_dec(v_a_1900_);
lean_inc(v_a_1875_);
v___f_1903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1903_, 0, v_a_1875_);
lean_closure_set(v___f_1903_, 1, v_e_1874_);
lean_closure_set(v___f_1903_, 2, v_fst_1901_);
v___x_1904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1903_, v_snd_1902_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1921_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1921_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1921_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_snd_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1919_; 
v_snd_1909_ = lean_ctor_get(v_a_1905_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v_a_1905_, 0);
lean_dec(v_unused_1920_);
v___x_1911_ = v_a_1905_;
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_snd_1909_);
lean_dec(v_a_1905_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v_fst_1901_);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_fst_1901_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_snd_1909_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1914_);
v___x_1916_ = v___x_1907_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_fst_1901_);
v_a_1922_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1904_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1904_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_dec_ref(v_e_1874_);
return v___x_1899_;
}
}
else
{
lean_object* v_val_1930_; lean_object* v___x_1932_; 
lean_dec_ref(v_e_1874_);
lean_dec_ref(v_post_1870_);
lean_dec_ref(v_pre_1869_);
v_val_1930_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v___x_1893_, 1);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_val_1930_);
v___x_1932_ = v___x_1891_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_val_1930_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_snd_1889_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1932_);
v___x_1934_ = v___x_1886_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_e_1874_);
lean_dec_ref(v_post_1870_);
lean_dec_ref(v_pre_1869_);
v_a_1939_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1883_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1883_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1947_, lean_object* v_pre_1948_, lean_object* v_post_1949_, lean_object* v_usedLetOnly_1950_, lean_object* v_skipConstInApp_1951_, lean_object* v_skipInstances_1952_, lean_object* v_body_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v_usedLetOnly_boxed_1962_; uint8_t v_skipConstInApp_boxed_1963_; uint8_t v_skipInstances_boxed_1964_; lean_object* v_res_1965_; 
v_usedLetOnly_boxed_1962_ = lean_unbox(v_usedLetOnly_1950_);
v_skipConstInApp_boxed_1963_ = lean_unbox(v_skipConstInApp_1951_);
v_skipInstances_boxed_1964_ = lean_unbox(v_skipInstances_1952_);
v_res_1965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1947_, v_pre_1948_, v_post_1949_, v_usedLetOnly_boxed_1962_, v_skipConstInApp_boxed_1963_, v_skipInstances_boxed_1964_, v_body_1953_, v_x_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1955_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1966_, lean_object* v_post_1967_, uint8_t v_usedLetOnly_1968_, uint8_t v_skipConstInApp_1969_, uint8_t v_skipInstances_1970_, lean_object* v_fvars_1971_, lean_object* v_e_1972_, lean_object* v_a_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
if (lean_obj_tag(v_e_1972_) == 7)
{
lean_object* v_binderName_1980_; lean_object* v_binderType_1981_; lean_object* v_body_1982_; uint8_t v_binderInfo_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_binderName_1980_ = lean_ctor_get(v_e_1972_, 0);
lean_inc(v_binderName_1980_);
v_binderType_1981_ = lean_ctor_get(v_e_1972_, 1);
lean_inc_ref(v_binderType_1981_);
v_body_1982_ = lean_ctor_get(v_e_1972_, 2);
lean_inc_ref(v_body_1982_);
v_binderInfo_1983_ = lean_ctor_get_uint8(v_e_1972_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1972_, 3);
v___x_1984_ = lean_expr_instantiate_rev(v_binderType_1981_, v_fvars_1971_);
lean_dec_ref(v_binderType_1981_);
lean_inc_ref(v_post_1967_);
lean_inc_ref(v_pre_1966_);
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1966_, v_post_1967_, v_usedLetOnly_1968_, v_skipConstInApp_1969_, v_skipInstances_1970_, v___x_1984_, v_a_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v_fst_1987_ = lean_ctor_get(v_a_1986_, 0);
lean_inc(v_fst_1987_);
v_snd_1988_ = lean_ctor_get(v_a_1986_, 1);
lean_inc(v_snd_1988_);
lean_dec(v_a_1986_);
v___x_1989_ = lean_box(v_usedLetOnly_1968_);
v___x_1990_ = lean_box(v_skipConstInApp_1969_);
v___x_1991_ = lean_box(v_skipInstances_1970_);
v___f_1992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1992_, 0, v_fvars_1971_);
lean_closure_set(v___f_1992_, 1, v_pre_1966_);
lean_closure_set(v___f_1992_, 2, v_post_1967_);
lean_closure_set(v___f_1992_, 3, v___x_1989_);
lean_closure_set(v___f_1992_, 4, v___x_1990_);
lean_closure_set(v___f_1992_, 5, v___x_1991_);
lean_closure_set(v___f_1992_, 6, v_body_1982_);
v___x_1993_ = 0;
v___x_1994_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(v_binderName_1980_, v_binderInfo_1983_, v_fst_1987_, v___f_1992_, v___x_1993_, v_a_1973_, v_snd_1988_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1994_;
}
else
{
lean_dec_ref(v_body_1982_);
lean_dec(v_binderName_1980_);
lean_dec_ref(v_fvars_1971_);
lean_dec_ref(v_post_1967_);
lean_dec_ref(v_pre_1966_);
return v___x_1985_;
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_expr_instantiate_rev(v_e_1972_, v_fvars_1971_);
lean_dec_ref(v_e_1972_);
lean_inc_ref(v_post_1967_);
lean_inc_ref(v_pre_1966_);
v___x_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1966_, v_post_1967_, v_usedLetOnly_1968_, v_skipConstInApp_1969_, v_skipInstances_1970_, v___x_1995_, v_a_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v_fst_1998_; lean_object* v_snd_1999_; uint8_t v___x_2000_; uint8_t v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v_fst_1998_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_fst_1998_);
v_snd_1999_ = lean_ctor_get(v_a_1997_, 1);
lean_inc(v_snd_1999_);
lean_dec(v_a_1997_);
v___x_2000_ = 0;
v___x_2001_ = 1;
v___x_2002_ = 1;
v___x_2003_ = l_Lean_Meta_mkForallFVars(v_fvars_1971_, v_fst_1998_, v___x_2000_, v_usedLetOnly_1968_, v___x_2001_, v___x_2002_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec_ref(v_fvars_1971_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1966_, v_post_1967_, v_usedLetOnly_1968_, v_skipConstInApp_1969_, v_skipInstances_1970_, v_a_2004_, v_a_1973_, v_snd_1999_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_2005_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_snd_1999_);
lean_dec_ref(v_post_1967_);
lean_dec_ref(v_pre_1966_);
v_a_2006_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2003_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2003_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1971_);
lean_dec_ref(v_post_1967_);
lean_dec_ref(v_pre_1966_);
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_2014_, lean_object* v_pre_2015_, lean_object* v_post_2016_, uint8_t v_usedLetOnly_2017_, uint8_t v_skipConstInApp_2018_, uint8_t v_skipInstances_2019_, lean_object* v_body_2020_, lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_array_push(v_fvars_2014_, v_x_2021_);
v___x_2030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_2015_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v___x_2029_, v_body_2020_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_2031_, lean_object* v_post_2032_, lean_object* v_usedLetOnly_2033_, lean_object* v_skipConstInApp_2034_, lean_object* v_skipInstances_2035_, lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_bs_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_usedLetOnly_boxed_2046_; uint8_t v_skipConstInApp_boxed_2047_; uint8_t v_skipInstances_boxed_2048_; size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_usedLetOnly_boxed_2046_ = lean_unbox(v_usedLetOnly_2033_);
v_skipConstInApp_boxed_2047_ = lean_unbox(v_skipConstInApp_2034_);
v_skipInstances_boxed_2048_ = lean_unbox(v_skipInstances_2035_);
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_2031_, v_post_2032_, v_usedLetOnly_boxed_2046_, v_skipConstInApp_boxed_2047_, v_skipInstances_boxed_2048_, v_sz_boxed_2049_, v_i_boxed_2050_, v_bs_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2039_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_2052_, lean_object* v_post_2053_, lean_object* v_usedLetOnly_2054_, lean_object* v_skipConstInApp_2055_, lean_object* v_skipInstances_2056_, lean_object* v_e_2057_, lean_object* v_a_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v_usedLetOnly_boxed_2065_; uint8_t v_skipConstInApp_boxed_2066_; uint8_t v_skipInstances_boxed_2067_; lean_object* v_res_2068_; 
v_usedLetOnly_boxed_2065_ = lean_unbox(v_usedLetOnly_2054_);
v_skipConstInApp_boxed_2066_ = lean_unbox(v_skipConstInApp_2055_);
v_skipInstances_boxed_2067_ = lean_unbox(v_skipInstances_2056_);
v_res_2068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_2052_, v_post_2053_, v_usedLetOnly_boxed_2065_, v_skipConstInApp_boxed_2066_, v_skipInstances_boxed_2067_, v_e_2057_, v_a_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v_a_2058_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_2069_, lean_object* v_post_2070_, lean_object* v_usedLetOnly_2071_, lean_object* v_skipConstInApp_2072_, lean_object* v_skipInstances_2073_, lean_object* v_fvars_2074_, lean_object* v_e_2075_, lean_object* v_a_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_usedLetOnly_boxed_2083_; uint8_t v_skipConstInApp_boxed_2084_; uint8_t v_skipInstances_boxed_2085_; lean_object* v_res_2086_; 
v_usedLetOnly_boxed_2083_ = lean_unbox(v_usedLetOnly_2071_);
v_skipConstInApp_boxed_2084_ = lean_unbox(v_skipConstInApp_2072_);
v_skipInstances_boxed_2085_ = lean_unbox(v_skipInstances_2073_);
v_res_2086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_2069_, v_post_2070_, v_usedLetOnly_boxed_2083_, v_skipConstInApp_boxed_2084_, v_skipInstances_boxed_2085_, v_fvars_2074_, v_e_2075_, v_a_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v_a_2076_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_2087_, lean_object* v_post_2088_, lean_object* v_usedLetOnly_2089_, lean_object* v_skipConstInApp_2090_, lean_object* v_skipInstances_2091_, lean_object* v_fvars_2092_, lean_object* v_e_2093_, lean_object* v_a_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v_usedLetOnly_boxed_2101_; uint8_t v_skipConstInApp_boxed_2102_; uint8_t v_skipInstances_boxed_2103_; lean_object* v_res_2104_; 
v_usedLetOnly_boxed_2101_ = lean_unbox(v_usedLetOnly_2089_);
v_skipConstInApp_boxed_2102_ = lean_unbox(v_skipConstInApp_2090_);
v_skipInstances_boxed_2103_ = lean_unbox(v_skipInstances_2091_);
v_res_2104_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_2087_, v_post_2088_, v_usedLetOnly_boxed_2101_, v_skipConstInApp_boxed_2102_, v_skipInstances_boxed_2103_, v_fvars_2092_, v_e_2093_, v_a_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_a_2094_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_2105_, lean_object* v_post_2106_, lean_object* v_usedLetOnly_2107_, lean_object* v_skipConstInApp_2108_, lean_object* v_skipInstances_2109_, lean_object* v_e_2110_, lean_object* v_a_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
uint8_t v_usedLetOnly_boxed_2118_; uint8_t v_skipConstInApp_boxed_2119_; uint8_t v_skipInstances_boxed_2120_; lean_object* v_res_2121_; 
v_usedLetOnly_boxed_2118_ = lean_unbox(v_usedLetOnly_2107_);
v_skipConstInApp_boxed_2119_ = lean_unbox(v_skipConstInApp_2108_);
v_skipInstances_boxed_2120_ = lean_unbox(v_skipInstances_2109_);
v_res_2121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2105_, v_post_2106_, v_usedLetOnly_boxed_2118_, v_skipConstInApp_boxed_2119_, v_skipInstances_boxed_2120_, v_e_2110_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v_a_2111_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_2122_, lean_object* v_post_2123_, lean_object* v_usedLetOnly_2124_, lean_object* v_skipConstInApp_2125_, lean_object* v_skipInstances_2126_, lean_object* v_fvars_2127_, lean_object* v_e_2128_, lean_object* v_a_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
uint8_t v_usedLetOnly_boxed_2136_; uint8_t v_skipConstInApp_boxed_2137_; uint8_t v_skipInstances_boxed_2138_; lean_object* v_res_2139_; 
v_usedLetOnly_boxed_2136_ = lean_unbox(v_usedLetOnly_2124_);
v_skipConstInApp_boxed_2137_ = lean_unbox(v_skipConstInApp_2125_);
v_skipInstances_boxed_2138_ = lean_unbox(v_skipInstances_2126_);
v_res_2139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_2122_, v_post_2123_, v_usedLetOnly_boxed_2136_, v_skipConstInApp_boxed_2137_, v_skipInstances_boxed_2138_, v_fvars_2127_, v_e_2128_, v_a_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_a_2129_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2140_, lean_object* v___x_2141_, lean_object* v_pre_2142_, lean_object* v_post_2143_, lean_object* v_usedLetOnly_2144_, lean_object* v_skipConstInApp_2145_, lean_object* v_skipInstances_2146_, lean_object* v_a_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_usedLetOnly_boxed_2156_; uint8_t v_skipConstInApp_boxed_2157_; uint8_t v_skipInstances_boxed_2158_; lean_object* v_res_2159_; 
v_usedLetOnly_boxed_2156_ = lean_unbox(v_usedLetOnly_2144_);
v_skipConstInApp_boxed_2157_ = lean_unbox(v_skipConstInApp_2145_);
v_skipInstances_boxed_2158_ = lean_unbox(v_skipInstances_2146_);
v_res_2159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2140_, v___x_2141_, v_pre_2142_, v_post_2143_, v_usedLetOnly_boxed_2156_, v_skipConstInApp_boxed_2157_, v_skipInstances_boxed_2158_, v_a_2147_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2149_);
lean_dec_ref(v___x_2141_);
lean_dec(v_upperBound_2140_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2160_, lean_object* v_pre_2161_, lean_object* v_post_2162_, lean_object* v_usedLetOnly_2163_, lean_object* v_skipConstInApp_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v_skipInstances_boxed_2175_; uint8_t v_usedLetOnly_boxed_2176_; uint8_t v_skipConstInApp_boxed_2177_; lean_object* v_res_2178_; 
v_skipInstances_boxed_2175_ = lean_unbox(v_skipInstances_2160_);
v_usedLetOnly_boxed_2176_ = lean_unbox(v_usedLetOnly_2163_);
v_skipConstInApp_boxed_2177_ = lean_unbox(v_skipConstInApp_2164_);
v_res_2178_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2175_, v_pre_2161_, v_post_2162_, v_usedLetOnly_boxed_2176_, v_skipConstInApp_boxed_2177_, v_x_2165_, v_x_2166_, v_x_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2168_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2179_, lean_object* v_x_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_apply_1(v_x_2180_, lean_box(0));
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___y_2181_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_x_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2190_, v_x_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2198_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_2199_; lean_object* v___x_2200_; 
v_cellCount_2199_ = lean_unsigned_to_nat(16u);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v_cellCount_2201_; lean_object* v___x_2202_; 
v_cellCount_2201_ = lean_unsigned_to_nat(16u);
v___x_2202_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2204_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2204_);
lean_ctor_set(v___x_2206_, 2, v___x_2203_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2208_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2208_, 0, lean_box(0));
lean_closure_set(v___x_2208_, 1, lean_box(0));
lean_closure_set(v___x_2208_, 2, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2209_, lean_object* v_pre_2210_, lean_object* v_post_2211_, uint8_t v_usedLetOnly_2212_, uint8_t v_skipConstInApp_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v_fst_2223_; lean_object* v_snd_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2220_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__3);
v___x_2221_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2220_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
v_fst_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_fst_2223_);
v_snd_2224_ = lean_ctor_get(v_a_2222_, 1);
lean_inc(v_snd_2224_);
lean_dec(v_a_2222_);
v___x_2225_ = 0;
v___x_2226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2210_, v_post_2211_, v_usedLetOnly_2212_, v_skipConstInApp_2213_, v___x_2225_, v_input_2209_, v_fst_2223_, v_snd_2224_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2248_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v_fst_2228_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_fst_2228_);
v_snd_2229_ = lean_ctor_get(v_a_2227_, 1);
lean_inc(v_snd_2229_);
lean_dec(v_a_2227_);
v___x_2230_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2230_, 0, lean_box(0));
lean_closure_set(v___x_2230_, 1, lean_box(0));
lean_closure_set(v___x_2230_, 2, v_fst_2223_);
v___x_2231_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2230_, v_snd_2229_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2248_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2248_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_snd_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2246_; 
v_snd_2236_ = lean_ctor_get(v_a_2232_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2232_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v_a_2232_, 0);
lean_dec(v_unused_2247_);
v___x_2238_ = v_a_2232_;
v_isShared_2239_ = v_isSharedCheck_2246_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_snd_2236_);
lean_dec(v_a_2232_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2246_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_fst_2228_);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_fst_2228_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_snd_2236_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2241_);
v___x_2243_ = v___x_2234_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_dec(v_fst_2223_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2249_, lean_object* v_pre_2250_, lean_object* v_post_2251_, lean_object* v_usedLetOnly_2252_, lean_object* v_skipConstInApp_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_usedLetOnly_boxed_2260_; uint8_t v_skipConstInApp_boxed_2261_; lean_object* v_res_2262_; 
v_usedLetOnly_boxed_2260_ = lean_unbox(v_usedLetOnly_2252_);
v_skipConstInApp_boxed_2261_ = lean_unbox(v_skipConstInApp_2253_);
v_res_2262_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2249_, v_pre_2250_, v_post_2251_, v_usedLetOnly_boxed_2260_, v_skipConstInApp_boxed_2261_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_keyedConfig_2271_; uint8_t v_trackZetaDelta_2272_; lean_object* v_zetaDeltaSet_2273_; lean_object* v_lctx_2274_; lean_object* v_localInstances_2275_; lean_object* v_defEqCtx_x3f_2276_; lean_object* v_synthPendingDepth_2277_; lean_object* v_customCanUnfoldPredicate_x3f_2278_; uint8_t v_univApprox_2279_; uint8_t v_inTypeClassResolution_2280_; uint8_t v_cacheInferType_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_keyedConfig_2271_ = lean_ctor_get(v_a_2266_, 0);
v_trackZetaDelta_2272_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7);
v_zetaDeltaSet_2273_ = lean_ctor_get(v_a_2266_, 1);
v_lctx_2274_ = lean_ctor_get(v_a_2266_, 2);
v_localInstances_2275_ = lean_ctor_get(v_a_2266_, 3);
v_defEqCtx_x3f_2276_ = lean_ctor_get(v_a_2266_, 4);
v_synthPendingDepth_2277_ = lean_ctor_get(v_a_2266_, 5);
v_customCanUnfoldPredicate_x3f_2278_ = lean_ctor_get(v_a_2266_, 6);
v_univApprox_2279_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2280_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 2);
v_cacheInferType_2281_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 3);
v___f_2282_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2283_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2284_ = 0;
v___x_2285_ = 3;
v___x_2286_ = lean_box(0);
lean_inc_ref(v_keyedConfig_2271_);
v___x_2287_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2285_, v_keyedConfig_2271_);
lean_inc(v_customCanUnfoldPredicate_x3f_2278_);
lean_inc(v_synthPendingDepth_2277_);
lean_inc(v_defEqCtx_x3f_2276_);
lean_inc_ref(v_localInstances_2275_);
lean_inc_ref(v_lctx_2274_);
lean_inc(v_zetaDeltaSet_2273_);
v___x_2288_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v_zetaDeltaSet_2273_);
lean_ctor_set(v___x_2288_, 2, v_lctx_2274_);
lean_ctor_set(v___x_2288_, 3, v_localInstances_2275_);
lean_ctor_set(v___x_2288_, 4, v_defEqCtx_x3f_2276_);
lean_ctor_set(v___x_2288_, 5, v_synthPendingDepth_2277_);
lean_ctor_set(v___x_2288_, 6, v_customCanUnfoldPredicate_x3f_2278_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*7, v_trackZetaDelta_2272_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*7 + 1, v_univApprox_2279_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2280_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*7 + 3, v_cacheInferType_2281_);
v___x_2289_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2265_, v___f_2283_, v___f_2282_, v___x_2284_, v___x_2284_, v___x_2286_, v___x_2288_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref_known(v___x_2288_, 7);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Meta_expandCoe(v_e_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2297_, lean_object* v_m_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2298_, v_a_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2301_, lean_object* v_m_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2301_, v_m_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_m_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
uint8_t v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2306_, v_x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
uint8_t v_res_2312_; lean_object* v_r_2313_; 
v_res_2312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2309_, v_x_2310_, v_x_2311_);
lean_dec_ref(v_x_2311_);
lean_dec_ref(v_x_2310_);
v_r_2313_ = lean_box(v_res_2312_);
return v_r_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2314_, lean_object* v_m_2315_, lean_object* v_query_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_m_2315_, v_query_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2318_, lean_object* v_m_2319_, lean_object* v_query_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2318_, v_m_2319_, v_query_2320_);
lean_dec(v_query_2320_);
lean_dec_ref(v_m_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2322_, lean_object* v___x_2323_, lean_object* v_pre_2324_, lean_object* v_post_2325_, uint8_t v_usedLetOnly_2326_, uint8_t v_skipConstInApp_2327_, uint8_t v_skipInstances_2328_, lean_object* v___x_2329_, lean_object* v_inst_2330_, lean_object* v_R_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_, lean_object* v_c_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2322_, v___x_2323_, v_pre_2324_, v_post_2325_, v_usedLetOnly_2326_, v_skipConstInApp_2327_, v_skipInstances_2328_, v_a_2332_, v_b_2333_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2343_ = _args[0];
lean_object* v___x_2344_ = _args[1];
lean_object* v_pre_2345_ = _args[2];
lean_object* v_post_2346_ = _args[3];
lean_object* v_usedLetOnly_2347_ = _args[4];
lean_object* v_skipConstInApp_2348_ = _args[5];
lean_object* v_skipInstances_2349_ = _args[6];
lean_object* v___x_2350_ = _args[7];
lean_object* v_inst_2351_ = _args[8];
lean_object* v_R_2352_ = _args[9];
lean_object* v_a_2353_ = _args[10];
lean_object* v_b_2354_ = _args[11];
lean_object* v_c_2355_ = _args[12];
lean_object* v___y_2356_ = _args[13];
lean_object* v___y_2357_ = _args[14];
lean_object* v___y_2358_ = _args[15];
lean_object* v___y_2359_ = _args[16];
lean_object* v___y_2360_ = _args[17];
lean_object* v___y_2361_ = _args[18];
lean_object* v___y_2362_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2363_; uint8_t v_skipConstInApp_boxed_2364_; uint8_t v_skipInstances_boxed_2365_; lean_object* v_res_2366_; 
v_usedLetOnly_boxed_2363_ = lean_unbox(v_usedLetOnly_2347_);
v_skipConstInApp_boxed_2364_ = lean_unbox(v_skipConstInApp_2348_);
v_skipInstances_boxed_2365_ = lean_unbox(v_skipInstances_2349_);
v_res_2366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2343_, v___x_2344_, v_pre_2345_, v_post_2346_, v_usedLetOnly_boxed_2363_, v_skipConstInApp_boxed_2364_, v_skipInstances_boxed_2365_, v___x_2350_, v_inst_2351_, v_R_2352_, v_a_2353_, v_b_2354_, v_c_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2356_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2344_);
lean_dec(v_upperBound_2343_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2367_, lean_object* v_m_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2368_, v_a_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2371_, lean_object* v_m_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2371_, v_m_2372_, v_a_2373_);
lean_dec_ref(v_a_2373_);
lean_dec_ref(v_m_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17(lean_object* v_00_u03b1_2375_, lean_object* v_name_2376_, uint8_t v_bi_2377_, lean_object* v_type_2378_, lean_object* v_k_2379_, uint8_t v_kind_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___redArg(v_name_2376_, v_bi_2377_, v_type_2378_, v_k_2379_, v_kind_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_name_2390_, lean_object* v_bi_2391_, lean_object* v_type_2392_, lean_object* v_k_2393_, lean_object* v_kind_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v_bi_boxed_2402_; uint8_t v_kind_boxed_2403_; lean_object* v_res_2404_; 
v_bi_boxed_2402_ = lean_unbox(v_bi_2391_);
v_kind_boxed_2403_ = lean_unbox(v_kind_2394_);
v_res_2404_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__17(v_00_u03b1_2389_, v_name_2390_, v_bi_boxed_2402_, v_type_2392_, v_k_2393_, v_kind_boxed_2403_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2395_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20(lean_object* v_00_u03b1_2405_, lean_object* v_name_2406_, lean_object* v_type_2407_, lean_object* v_val_2408_, lean_object* v_k_2409_, uint8_t v_nondep_2410_, uint8_t v_kind_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___redArg(v_name_2406_, v_type_2407_, v_val_2408_, v_k_2409_, v_nondep_2410_, v_kind_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_name_2421_, lean_object* v_type_2422_, lean_object* v_val_2423_, lean_object* v_k_2424_, lean_object* v_nondep_2425_, lean_object* v_kind_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_nondep_boxed_2434_; uint8_t v_kind_boxed_2435_; lean_object* v_res_2436_; 
v_nondep_boxed_2434_ = lean_unbox(v_nondep_2425_);
v_kind_boxed_2435_ = lean_unbox(v_kind_2426_);
v_res_2436_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__20(v_00_u03b1_2420_, v_name_2421_, v_type_2422_, v_val_2423_, v_k_2424_, v_nondep_boxed_2434_, v_kind_boxed_2435_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2427_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23(lean_object* v_00_u03b1_2437_, lean_object* v_ref_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___redArg(v_ref_2438_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_ref_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__23(v_00_u03b1_2445_, v_ref_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_x_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2463_, v_x_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2465_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2473_, lean_object* v_m_2474_, lean_object* v_query_2475_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2474_, v_query_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object* v_00_u03b2_2477_, lean_object* v_m_2478_, lean_object* v_query_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(v_00_u03b2_2477_, v_m_2478_, v_query_2479_);
lean_dec_ref(v_query_2479_);
lean_dec_ref(v_m_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object* v_00_u03b2_2481_, lean_object* v_m_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___boxed(lean_object* v_00_u03b2_2484_, lean_object* v_m_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(v_00_u03b2_2484_, v_m_2485_);
lean_dec_ref(v_m_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2487_, lean_object* v_x_2488_, size_t v_x_2489_, lean_object* v_x_2490_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2488_, v_x_2489_, v_x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
size_t v_x_41904__boxed_2496_; uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_x_41904__boxed_2496_ = lean_unbox_usize(v_x_2494_);
lean_dec(v_x_2494_);
v_res_2497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2492_, v_x_2493_, v_x_41904__boxed_2496_, v_x_2495_);
lean_dec_ref(v_x_2495_);
lean_dec_ref(v_x_2493_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2499_, lean_object* v_m_2500_, lean_object* v_query_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___redArg(v_m_2500_, v_query_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2503_, lean_object* v_m_2504_, lean_object* v_query_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9(v_00_u03b2_2503_, v_m_2504_, v_query_2505_);
lean_dec(v_query_2505_);
lean_dec_ref(v_m_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15(lean_object* v_00_u03b2_2507_, lean_object* v_m_2508_, lean_object* v_query_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___redArg(v_m_2508_, v_query_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2511_, lean_object* v_m_2512_, lean_object* v_query_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__15(v_00_u03b2_2511_, v_m_2512_, v_query_2513_);
lean_dec_ref(v_query_2513_);
lean_dec_ref(v_m_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2515_, lean_object* v_m_2516_, lean_object* v_query_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_m_2516_, v_query_2517_, v_x_2518_, v_x_2519_, v_x_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___boxed(lean_object* v_00_u03b2_2523_, lean_object* v_m_2524_, lean_object* v_query_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(v_00_u03b2_2523_, v_m_2524_, v_query_2525_, v_x_2526_, v_x_2527_, v_x_2528_, v_x_2529_);
lean_dec_ref(v_query_2525_);
lean_dec_ref(v_m_2524_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2531_, lean_object* v_init_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_init_2532_, v_b_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___boxed(lean_object* v_00_u03b2_2535_, lean_object* v_init_2536_, lean_object* v_b_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(v_00_u03b2_2535_, v_init_2536_, v_b_2537_);
lean_dec_ref(v_b_2537_);
return v_res_2538_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2539_, lean_object* v_keys_2540_, lean_object* v_vals_2541_, lean_object* v_heq_2542_, lean_object* v_i_2543_, lean_object* v_k_2544_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2540_, v_i_2543_, v_k_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2546_, lean_object* v_keys_2547_, lean_object* v_vals_2548_, lean_object* v_heq_2549_, lean_object* v_i_2550_, lean_object* v_k_2551_){
_start:
{
uint8_t v_res_2552_; lean_object* v_r_2553_; 
v_res_2552_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2546_, v_keys_2547_, v_vals_2548_, v_heq_2549_, v_i_2550_, v_k_2551_);
lean_dec_ref(v_k_2551_);
lean_dec_ref(v_vals_2548_);
lean_dec_ref(v_keys_2547_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_2554_, lean_object* v_m_2555_, lean_object* v_query_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___redArg(v_m_2555_, v_query_2556_, v_x_2557_, v_x_2558_, v_x_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b2_2562_, lean_object* v_m_2563_, lean_object* v_query_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5_spec__9_spec__12(v_00_u03b2_2562_, v_m_2563_, v_query_2564_, v_x_2565_, v_x_2566_, v_x_2567_, v_x_2568_);
lean_dec(v_query_2564_);
lean_dec_ref(v_m_2563_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30(lean_object* v_00_u03b2_2570_, lean_object* v_b_2571_, lean_object* v_acc_2572_, lean_object* v_i_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___redArg(v_b_2571_, v_acc_2572_, v_i_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30___boxed(lean_object* v_00_u03b2_2575_, lean_object* v_b_2576_, lean_object* v_acc_2577_, lean_object* v_i_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27_spec__30(v_00_u03b2_2575_, v_b_2576_, v_acc_2577_, v_i_2578_);
lean_dec_ref(v_b_2576_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2580_, lean_object* v_decl_2581_, lean_object* v_ref_2582_){
_start:
{
lean_object* v_defValue_2584_; lean_object* v_descr_2585_; lean_object* v_deprecation_x3f_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_defValue_2584_ = lean_ctor_get(v_decl_2581_, 0);
v_descr_2585_ = lean_ctor_get(v_decl_2581_, 1);
v_deprecation_x3f_2586_ = lean_ctor_get(v_decl_2581_, 2);
v___x_2587_ = lean_alloc_ctor(1, 0, 1);
v___x_2588_ = lean_unbox(v_defValue_2584_);
lean_ctor_set_uint8(v___x_2587_, 0, v___x_2588_);
lean_inc(v_deprecation_x3f_2586_);
lean_inc_ref(v_descr_2585_);
lean_inc_n(v_name_2580_, 2);
v___x_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2589_, 0, v_name_2580_);
lean_ctor_set(v___x_2589_, 1, v_ref_2582_);
lean_ctor_set(v___x_2589_, 2, v___x_2587_);
lean_ctor_set(v___x_2589_, 3, v_descr_2585_);
lean_ctor_set(v___x_2589_, 4, v_deprecation_x3f_2586_);
v___x_2590_ = lean_register_option(v_name_2580_, v___x_2589_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2598_; 
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2599_);
v___x_2592_ = v___x_2590_;
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
else
{
lean_dec(v___x_2590_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2598_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_inc(v_defValue_2584_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_name_2580_);
lean_ctor_set(v___x_2594_, 1, v_defValue_2584_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2594_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_name_2580_);
v_a_2600_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2590_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2590_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2608_, lean_object* v_decl_2609_, lean_object* v_ref_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2608_, v_decl_2609_, v_ref_2610_);
lean_dec_ref(v_decl_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2627_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2630_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2627_, v___x_2628_, v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_ref_2639_; lean_object* v___x_2640_; lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2649_; 
v_ref_2639_ = lean_ctor_get(v___y_2636_, 5);
v___x_2640_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2649_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2649_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_inc(v_ref_2639_);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v_ref_2639_);
lean_ctor_set(v___x_2645_, 1, v_a_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
lean_ctor_set(v___x_2643_, 0, v___x_2645_);
v___x_2647_ = v___x_2643_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2672_, lean_object* v_expectedType_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; 
lean_inc(v_a_2677_);
lean_inc_ref(v_a_2676_);
lean_inc(v_a_2675_);
lean_inc_ref(v_a_2674_);
lean_inc_ref(v_expr_2672_);
v___x_2679_ = lean_infer_type(v_expr_2672_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc_n(v_a_2680_, 2);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = l_Lean_Meta_getLevel(v_a_2680_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
lean_inc_ref(v_expectedType_2673_);
v___x_2683_ = l_Lean_Meta_getLevel(v_expectedType_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2687_, 0, v_a_2684_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_a_2682_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
lean_inc_ref(v___x_2688_);
v___x_2689_ = l_Lean_mkConst(v___x_2685_, v___x_2688_);
v___x_2690_ = lean_unsigned_to_nat(3u);
v___x_2691_ = lean_mk_empty_array_with_capacity(v___x_2690_);
lean_inc(v_a_2680_);
v___x_2692_ = lean_array_push(v___x_2691_, v_a_2680_);
lean_inc_ref(v_expr_2672_);
v___x_2693_ = lean_array_push(v___x_2692_, v_expr_2672_);
lean_inc_ref(v_expectedType_2673_);
v___x_2694_ = lean_array_push(v___x_2693_, v_expectedType_2673_);
v___x_2695_ = l_Lean_mkAppN(v___x_2689_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = lean_box(0);
v___x_2697_ = l_Lean_Meta_trySynthInstance(v___x_2695_, v___x_2696_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2795_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2795_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2795_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
switch(lean_obj_tag(v_a_2698_))
{
case 0:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_dec_ref_known(v___x_2688_, 2);
lean_dec(v_a_2680_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v___x_2702_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
case 1:
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2700_);
v_a_2706_ = lean_ctor_get(v_a_2698_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_a_2698_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2708_ = v_a_2698_;
v_isShared_2709_ = v_isSharedCheck_2790_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v_a_2698_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2790_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2710_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2711_ = l_Lean_mkConst(v___x_2710_, v___x_2688_);
v___x_2712_ = lean_unsigned_to_nat(4u);
v___x_2713_ = lean_mk_empty_array_with_capacity(v___x_2712_);
v___x_2714_ = lean_array_push(v___x_2713_, v_a_2680_);
lean_inc_ref(v_expr_2672_);
v___x_2715_ = lean_array_push(v___x_2714_, v_expr_2672_);
lean_inc_ref(v_expectedType_2673_);
v___x_2716_ = lean_array_push(v___x_2715_, v_expectedType_2673_);
v___x_2717_ = lean_array_push(v___x_2716_, v_a_2706_);
v___x_2718_ = l_Lean_mkAppN(v___x_2711_, v___x_2717_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = l_Lean_Meta_expandCoe(v___x_2718_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2781_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2781_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2781_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_fst_2731_; lean_object* v___x_2732_; 
v_fst_2731_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_a_2677_);
lean_inc_ref(v_a_2676_);
lean_inc(v_a_2675_);
lean_inc_ref(v_a_2674_);
lean_inc(v_fst_2731_);
v___x_2732_ = lean_infer_type(v_fst_2731_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
lean_inc_ref(v_expectedType_2673_);
v___x_2734_ = l_Lean_Meta_isExprDefEq(v_a_2733_, v_expectedType_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = lean_unbox(v_a_2735_);
lean_dec(v_a_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2762_; 
lean_inc(v_fst_2731_);
lean_del_object(v___x_2722_);
lean_del_object(v___x_2708_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2720_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; lean_object* v_unused_2764_; 
v_unused_2763_ = lean_ctor_get(v_a_2720_, 1);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_a_2720_, 0);
lean_dec(v_unused_2764_);
v___x_2738_ = v_a_2720_;
v_isShared_2739_ = v_isSharedCheck_2762_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_a_2720_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2762_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2740_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2741_ = l_Lean_indentExpr(v_expr_2672_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 7);
lean_ctor_set(v___x_2738_, 1, v___x_2741_);
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2743_ = v___x_2738_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v___x_2744_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_indentExpr(v_expectedType_2673_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Lean_indentExpr(v_fst_2731_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2751_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
goto v___jp_2724_;
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_del_object(v___x_2722_);
lean_dec(v_a_2720_);
lean_del_object(v___x_2708_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2765_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2734_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2734_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_del_object(v___x_2722_);
lean_dec(v_a_2720_);
lean_del_object(v___x_2708_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2773_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2732_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2732_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
v___jp_2724_:
{
lean_object* v___x_2726_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v_a_2720_);
v___x_2726_ = v___x_2708_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2720_);
v___x_2726_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2726_);
v___x_2728_ = v___x_2722_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_del_object(v___x_2708_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2782_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2719_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2719_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
default: 
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_dec_ref_known(v___x_2688_, 2);
lean_dec(v_a_2680_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v___x_2791_ = lean_box(2);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2791_);
v___x_2793_ = v___x_2700_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref_known(v___x_2688_, 2);
lean_dec(v_a_2680_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2796_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2697_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2697_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2682_);
lean_dec(v_a_2680_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2804_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2683_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2683_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2680_);
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2812_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2681_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2681_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_expectedType_2673_);
lean_dec_ref(v_expr_2672_);
v_a_2820_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2679_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2679_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2828_, lean_object* v_expectedType_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2828_, v_expectedType_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2836_, lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2844_, lean_object* v_msg_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2844_, v_msg_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2852_, lean_object* v_expectedType_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2852_, v_expectedType_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2884_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
switch(lean_obj_tag(v_a_2860_))
{
case 0:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = lean_box(0);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2864_);
v___x_2866_ = v___x_2862_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
case 1:
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2879_; 
v_a_2868_ = lean_ctor_get(v_a_2860_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_a_2860_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2870_ = v_a_2860_;
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v_a_2860_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2879_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_fst_2872_; lean_object* v___x_2874_; 
v_fst_2872_ = lean_ctor_get(v_a_2868_, 0);
lean_inc(v_fst_2872_);
lean_dec(v_a_2868_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_fst_2872_);
v___x_2874_ = v___x_2870_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_fst_2872_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2874_);
v___x_2876_ = v___x_2862_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
default: 
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_box(2);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2880_);
v___x_2882_ = v___x_2862_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_a_2885_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2859_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2859_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2893_, lean_object* v_expectedType_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2893_, v_expectedType_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2900_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
return v___x_2912_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2922_; 
lean_inc(v_a_2920_);
lean_inc_ref(v_a_2919_);
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
lean_inc_ref(v_expr_2916_);
v___x_2922_ = lean_infer_type(v_expr_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_n(v_a_2923_, 2);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Meta_getLevel(v_a_2923_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_n(v_a_2927_, 2);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = l_Lean_mkSort(v_a_2927_);
lean_inc(v_a_2923_);
v___x_2929_ = l_Lean_mkArrow(v_a_2923_, v___x_2928_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_a_2930_);
v___x_2932_ = 0;
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_Meta_mkFreshExprMVar(v___x_2931_, v___x_2932_, v___x_2933_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc_n(v_a_2935_, 2);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2938_, 0, v_a_2927_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2925_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_inc_ref(v___x_2939_);
v___x_2940_ = l_Lean_Expr_const___override(v___x_2936_, v___x_2939_);
lean_inc(v_a_2923_);
v___x_2941_ = l_Lean_mkAppB(v___x_2940_, v_a_2923_, v_a_2935_);
v___x_2942_ = lean_box(0);
v___x_2943_ = l_Lean_Meta_trySynthInstance(v___x_2941_, v___x_2942_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3030_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_3030_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3030_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
if (lean_obj_tag(v_a_2944_) == 1)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2946_);
v_a_2948_ = lean_ctor_get(v_a_2944_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2950_ = v_a_2944_;
v_isShared_2951_ = v_isSharedCheck_3026_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v_a_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3026_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2952_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2953_ = l_Lean_Expr_const___override(v___x_2952_, v___x_2939_);
lean_inc_ref(v_expr_2916_);
lean_inc(v_a_2948_);
v___x_2954_ = l_Lean_mkApp4(v___x_2953_, v_a_2923_, v_a_2935_, v_a_2948_, v_expr_2916_);
v___x_2955_ = l_Lean_Meta_expandCoe(v___x_2954_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3017_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_3017_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3017_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v_fst_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3015_; 
v_fst_2960_ = lean_ctor_get(v_a_2956_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_a_2956_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_a_2956_, 1);
lean_dec(v_unused_3016_);
v___x_2962_ = v_a_2956_;
v_isShared_2963_ = v_isSharedCheck_3015_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_fst_2960_);
lean_dec(v_a_2956_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3015_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2971_; 
lean_inc(v_a_2920_);
lean_inc_ref(v_a_2919_);
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
lean_inc(v_fst_2960_);
v___x_2971_ = lean_infer_type(v_fst_2960_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
lean_inc(v_a_2920_);
lean_inc_ref(v_a_2919_);
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
v___x_2973_ = lean_whnf(v_a_2972_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; uint8_t v___x_2975_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = l_Lean_Expr_isForall(v_a_2974_);
lean_dec(v_a_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
lean_del_object(v___x_2958_);
lean_del_object(v___x_2950_);
v___x_2976_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2977_ = l_Lean_indentExpr(v_expr_2916_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 7);
lean_ctor_set(v___x_2962_, 1, v___x_2977_);
lean_ctor_set(v___x_2962_, 0, v___x_2976_);
v___x_2979_ = v___x_2962_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v___x_2980_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = l_Lean_indentExpr(v_fst_2960_);
v___x_2983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2985_ = l_Lean_indentExpr(v_a_2948_);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_MessageData_hint_x27(v___x_2986_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2983_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2988_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_del_object(v___x_2962_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2916_);
goto v___jp_2964_;
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_del_object(v___x_2962_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_del_object(v___x_2950_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2916_);
v_a_2999_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2973_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2973_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2962_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2958_);
lean_del_object(v___x_2950_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2916_);
v_a_3007_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2971_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2971_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
v___jp_2964_:
{
lean_object* v___x_2966_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v_fst_2960_);
v___x_2966_ = v___x_2950_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_fst_2960_);
v___x_2966_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2966_);
v___x_2968_ = v___x_2958_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_del_object(v___x_2950_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2916_);
v_a_3018_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2955_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2955_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
else
{
lean_object* v___x_3028_; 
lean_dec(v_a_2944_);
lean_dec_ref_known(v___x_2939_, 2);
lean_dec(v_a_2935_);
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2942_);
v___x_3028_ = v___x_2946_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_2942_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref_known(v___x_2939_, 2);
lean_dec(v_a_2935_);
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
v_a_3031_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2943_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2943_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_a_2927_);
lean_dec(v_a_2925_);
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
v_a_3039_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_2934_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_2934_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_2927_);
lean_dec(v_a_2925_);
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
v_a_3047_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2929_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2929_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
v_a_3055_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2926_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2926_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_2923_);
lean_dec_ref(v_expr_2916_);
v_a_3063_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2924_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2924_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_expr_2916_);
v_a_3071_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2922_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2922_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3085_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_3097_ = l_Lean_stringToMessageData(v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; 
lean_inc(v_a_3102_);
lean_inc_ref(v_a_3101_);
lean_inc(v_a_3100_);
lean_inc_ref(v_a_3099_);
lean_inc_ref(v_expr_3098_);
v___x_3104_ = lean_infer_type(v_expr_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_n(v_a_3105_, 2);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = l_Lean_Meta_getLevel(v_a_3105_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Meta_mkFreshLevelMVar(v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc_n(v_a_3109_, 2);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = l_Lean_mkSort(v_a_3109_);
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
v___x_3112_ = 0;
v___x_3113_ = lean_box(0);
v___x_3114_ = l_Lean_Meta_mkFreshExprMVar(v___x_3111_, v___x_3112_, v___x_3113_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc_n(v_a_3115_, 2);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_a_3109_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_a_3107_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
lean_inc_ref(v___x_3119_);
v___x_3120_ = l_Lean_Expr_const___override(v___x_3116_, v___x_3119_);
lean_inc(v_a_3105_);
v___x_3121_ = l_Lean_mkAppB(v___x_3120_, v_a_3105_, v_a_3115_);
v___x_3122_ = lean_box(0);
v___x_3123_ = l_Lean_Meta_trySynthInstance(v___x_3121_, v___x_3122_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3210_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3210_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3210_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
if (lean_obj_tag(v_a_3124_) == 1)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_3126_);
v_a_3128_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3130_ = v_a_3124_;
v_isShared_3131_ = v_isSharedCheck_3206_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v_a_3124_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3206_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3133_ = l_Lean_Expr_const___override(v___x_3132_, v___x_3119_);
lean_inc_ref(v_expr_3098_);
lean_inc(v_a_3128_);
v___x_3134_ = l_Lean_mkApp4(v___x_3133_, v_a_3105_, v_a_3115_, v_a_3128_, v_expr_3098_);
v___x_3135_ = l_Lean_Meta_expandCoe(v___x_3134_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3197_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3197_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3197_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_fst_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3195_; 
v_fst_3140_ = lean_ctor_get(v_a_3136_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_a_3136_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_a_3136_, 1);
lean_dec(v_unused_3196_);
v___x_3142_ = v_a_3136_;
v_isShared_3143_ = v_isSharedCheck_3195_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_fst_3140_);
lean_dec(v_a_3136_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3195_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3151_; 
lean_inc(v_a_3102_);
lean_inc_ref(v_a_3101_);
lean_inc(v_a_3100_);
lean_inc_ref(v_a_3099_);
lean_inc(v_fst_3140_);
v___x_3151_ = lean_infer_type(v_fst_3140_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
lean_inc(v_a_3102_);
lean_inc_ref(v_a_3101_);
lean_inc(v_a_3100_);
lean_inc_ref(v_a_3099_);
v___x_3153_ = lean_whnf(v_a_3152_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; uint8_t v___x_3155_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = l_Lean_Expr_isSort(v_a_3154_);
lean_dec(v_a_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_del_object(v___x_3138_);
lean_del_object(v___x_3130_);
v___x_3156_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3157_ = l_Lean_indentExpr(v_expr_3098_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 7);
lean_ctor_set(v___x_3142_, 1, v___x_3157_);
lean_ctor_set(v___x_3142_, 0, v___x_3156_);
v___x_3159_ = v___x_3142_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v___x_3160_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Lean_indentExpr(v_fst_3140_);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3165_ = l_Lean_indentExpr(v_a_3128_);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = l_Lean_MessageData_hint_x27(v___x_3166_);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3163_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3168_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_del_object(v___x_3142_);
lean_dec(v_a_3128_);
lean_dec_ref(v_expr_3098_);
goto v___jp_3144_;
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_del_object(v___x_3142_);
lean_dec(v_fst_3140_);
lean_del_object(v___x_3138_);
lean_del_object(v___x_3130_);
lean_dec(v_a_3128_);
lean_dec_ref(v_expr_3098_);
v_a_3179_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3153_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3153_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_3142_);
lean_dec(v_fst_3140_);
lean_del_object(v___x_3138_);
lean_del_object(v___x_3130_);
lean_dec(v_a_3128_);
lean_dec_ref(v_expr_3098_);
v_a_3187_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3151_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3151_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
v___jp_3144_:
{
lean_object* v___x_3146_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_fst_3140_);
v___x_3146_ = v___x_3130_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_fst_3140_);
v___x_3146_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3148_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3146_);
v___x_3148_ = v___x_3138_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_del_object(v___x_3130_);
lean_dec(v_a_3128_);
lean_dec_ref(v_expr_3098_);
v_a_3198_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3135_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3135_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
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
}
else
{
lean_object* v___x_3208_; 
lean_dec(v_a_3124_);
lean_dec_ref_known(v___x_3119_, 2);
lean_dec(v_a_3115_);
lean_dec(v_a_3105_);
lean_dec_ref(v_expr_3098_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3122_);
v___x_3208_ = v___x_3126_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3122_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref_known(v___x_3119_, 2);
lean_dec(v_a_3115_);
lean_dec(v_a_3105_);
lean_dec_ref(v_expr_3098_);
v_a_3211_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3123_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3123_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3105_);
lean_dec_ref(v_expr_3098_);
v_a_3219_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3114_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3114_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3105_);
lean_dec_ref(v_expr_3098_);
v_a_3227_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3108_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3108_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_a_3105_);
lean_dec_ref(v_expr_3098_);
v_a_3235_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3106_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3106_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_expr_3098_);
v_a_3243_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3104_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3104_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_Expr_hasMVar(v_e_3258_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_e_3258_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; lean_object* v_mctx_3264_; lean_object* v___x_3265_; lean_object* v_fst_3266_; lean_object* v_snd_3267_; lean_object* v___x_3268_; lean_object* v_cache_3269_; lean_object* v_zetaDeltaFVarIds_3270_; lean_object* v_postponed_3271_; lean_object* v_diag_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3281_; 
v___x_3263_ = lean_st_ref_get(v___y_3259_);
v_mctx_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_mctx_3264_);
lean_dec(v___x_3263_);
v___x_3265_ = l_Lean_instantiateMVarsCore(v_mctx_3264_, v_e_3258_);
v_fst_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_fst_3266_);
v_snd_3267_ = lean_ctor_get(v___x_3265_, 1);
lean_inc(v_snd_3267_);
lean_dec_ref(v___x_3265_);
v___x_3268_ = lean_st_ref_take(v___y_3259_);
v_cache_3269_ = lean_ctor_get(v___x_3268_, 1);
v_zetaDeltaFVarIds_3270_ = lean_ctor_get(v___x_3268_, 2);
v_postponed_3271_ = lean_ctor_get(v___x_3268_, 3);
v_diag_3272_ = lean_ctor_get(v___x_3268_, 4);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v___x_3268_, 0);
lean_dec(v_unused_3282_);
v___x_3274_ = v___x_3268_;
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_diag_3272_);
lean_inc(v_postponed_3271_);
lean_inc(v_zetaDeltaFVarIds_3270_);
lean_inc(v_cache_3269_);
lean_dec(v___x_3268_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_snd_3267_);
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_snd_3267_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_cache_3269_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_zetaDeltaFVarIds_3270_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_postponed_3271_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_diag_3272_);
v___x_3277_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_st_ref_put(v___y_3259_, v___x_3277_);
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_fst_3266_);
return v___x_3279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3283_, v___y_3284_);
lean_dec(v___y_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3287_, v___y_3289_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_keyedConfig_3307_; uint8_t v_trackZetaDelta_3308_; lean_object* v_zetaDeltaSet_3309_; lean_object* v_lctx_3310_; lean_object* v_localInstances_3311_; lean_object* v_defEqCtx_x3f_3312_; lean_object* v_synthPendingDepth_3313_; lean_object* v_customCanUnfoldPredicate_x3f_3314_; uint8_t v_univApprox_3315_; uint8_t v_inTypeClassResolution_3316_; uint8_t v_cacheInferType_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_keyedConfig_3307_ = lean_ctor_get(v_a_3302_, 0);
v_trackZetaDelta_3308_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7);
v_zetaDeltaSet_3309_ = lean_ctor_get(v_a_3302_, 1);
v_lctx_3310_ = lean_ctor_get(v_a_3302_, 2);
v_localInstances_3311_ = lean_ctor_get(v_a_3302_, 3);
v_defEqCtx_x3f_3312_ = lean_ctor_get(v_a_3302_, 4);
v_synthPendingDepth_3313_ = lean_ctor_get(v_a_3302_, 5);
v_customCanUnfoldPredicate_x3f_3314_ = lean_ctor_get(v_a_3302_, 6);
v_univApprox_3315_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3316_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 2);
v_cacheInferType_3317_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 3);
v___x_3318_ = 2;
lean_inc_ref(v_keyedConfig_3307_);
v___x_3319_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3318_, v_keyedConfig_3307_);
lean_inc(v_customCanUnfoldPredicate_x3f_3314_);
lean_inc(v_synthPendingDepth_3313_);
lean_inc(v_defEqCtx_x3f_3312_);
lean_inc_ref(v_localInstances_3311_);
lean_inc_ref(v_lctx_3310_);
lean_inc(v_zetaDeltaSet_3309_);
v___x_3320_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v_zetaDeltaSet_3309_);
lean_ctor_set(v___x_3320_, 2, v_lctx_3310_);
lean_ctor_set(v___x_3320_, 3, v_localInstances_3311_);
lean_ctor_set(v___x_3320_, 4, v_defEqCtx_x3f_3312_);
lean_ctor_set(v___x_3320_, 5, v_synthPendingDepth_3313_);
lean_ctor_set(v___x_3320_, 6, v_customCanUnfoldPredicate_x3f_3314_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7, v_trackZetaDelta_3308_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 1, v_univApprox_3315_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3316_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7 + 3, v_cacheInferType_3317_);
lean_inc(v_a_3305_);
lean_inc_ref(v_a_3304_);
lean_inc(v_a_3303_);
v___x_3321_ = lean_whnf(v_type_3301_, v___x_3320_, v_a_3303_, v_a_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3351_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3351_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3351_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
if (lean_obj_tag(v_a_3322_) == 5)
{
lean_object* v_fn_3326_; lean_object* v_arg_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3346_; 
lean_del_object(v___x_3324_);
v_fn_3326_ = lean_ctor_get(v_a_3322_, 0);
lean_inc_ref(v_fn_3326_);
v_arg_3327_ = lean_ctor_get(v_a_3322_, 1);
lean_inc_ref(v_arg_3327_);
lean_dec_ref_known(v_a_3322_, 2);
v___x_3328_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3326_, v_a_3303_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3345_; 
v___x_3333_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3327_, v_a_3303_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3329_);
lean_ctor_set(v___x_3338_, 1, v_a_3334_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 1);
lean_ctor_set(v___x_3331_, 0, v___x_3338_);
v___x_3340_ = v___x_3331_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3340_);
v___x_3342_ = v___x_3336_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_dec(v_a_3322_);
v___x_3347_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3347_);
v___x_3349_ = v___x_3324_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_a_3352_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3321_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3321_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Meta_isTypeApp_x3f(v_type_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_isTypeApp_x3f(v_type_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3409_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3409_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3409_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
if (lean_obj_tag(v_a_3374_) == 1)
{
lean_object* v_val_3378_; lean_object* v_fst_3379_; lean_object* v___x_3380_; 
lean_del_object(v___x_3376_);
v_val_3378_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v_a_3374_, 1);
v_fst_3379_ = lean_ctor_get(v_val_3378_, 0);
lean_inc(v_fst_3379_);
lean_dec(v_val_3378_);
v___x_3380_ = l_Lean_Meta_isMonad_x3f(v_fst_3379_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3395_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3395_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3395_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_a_3381_) == 0)
{
uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3385_ = 0;
v___x_3386_ = lean_box(v___x_3385_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3386_);
v___x_3388_ = v___x_3383_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
else
{
uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
lean_dec_ref_known(v_a_3381_, 1);
v___x_3390_ = 1;
v___x_3391_ = lean_box(v___x_3390_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3391_);
v___x_3393_ = v___x_3383_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_a_3396_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3380_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3380_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v_a_3374_);
v___x_3404_ = 0;
v___x_3405_ = lean_box(v___x_3404_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3405_);
v___x_3407_ = v___x_3376_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_a_3410_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3373_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3373_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Meta_isMonadApp(v_type_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3425_, lean_object* v_opt_3426_){
_start:
{
lean_object* v_name_3427_; lean_object* v_defValue_3428_; lean_object* v_map_3429_; lean_object* v___x_3430_; 
v_name_3427_ = lean_ctor_get(v_opt_3426_, 0);
v_defValue_3428_ = lean_ctor_get(v_opt_3426_, 1);
v_map_3429_ = lean_ctor_get(v_opts_3425_, 0);
v___x_3430_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3429_, v_name_3427_);
if (lean_obj_tag(v___x_3430_) == 0)
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_unbox(v_defValue_3428_);
return v___x_3431_;
}
else
{
lean_object* v_val_3432_; 
v_val_3432_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_val_3432_);
lean_dec_ref_known(v___x_3430_, 1);
if (lean_obj_tag(v_val_3432_) == 1)
{
uint8_t v_v_3433_; 
v_v_3433_ = lean_ctor_get_uint8(v_val_3432_, 0);
lean_dec_ref_known(v_val_3432_, 0);
return v_v_3433_;
}
else
{
uint8_t v___x_3434_; 
lean_dec(v_val_3432_);
v___x_3434_ = lean_unbox(v_defValue_3428_);
return v___x_3434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3435_, lean_object* v_opt_3436_){
_start:
{
uint8_t v_res_3437_; lean_object* v_r_3438_; 
v_res_3437_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3435_, v_opt_3436_);
lean_dec_ref(v_opt_3436_);
lean_dec_ref(v_opts_3435_);
v_r_3438_ = lean_box(v_res_3437_);
return v_r_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_x_3449_);
return v_res_3455_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = l_Lean_mkBVar(v___x_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3478_, lean_object* v_expectedType_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___y_3486_; uint8_t v___y_3487_; lean_object* v_a_3492_; lean_object* v___y_3496_; lean_object* v___x_3506_; lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3910_; 
v___x_3506_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3479_, v_a_3481_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3910_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3910_;
goto v_resetjp_3508_;
}
v___jp_3485_:
{
if (v___y_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec_ref(v___y_3486_);
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
else
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___y_3486_);
return v___x_3490_;
}
}
v___jp_3491_:
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Lean_Exception_isInterrupt(v_a_3492_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
lean_inc_ref(v_a_3492_);
v___x_3494_ = l_Lean_Exception_isRuntime(v_a_3492_);
v___y_3486_ = v_a_3492_;
v___y_3487_ = v___x_3494_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v_a_3492_;
v___y_3487_ = v___x_3493_;
goto v___jp_3485_;
}
}
v___jp_3495_:
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3505_; 
v_a_3497_ = lean_ctor_get(v___y_3496_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___y_3496_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3499_ = v___y_3496_;
v_isShared_3500_ = v_isSharedCheck_3505_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___y_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3505_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_a_3501_; lean_object* v___x_3503_; 
v_a_3501_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_a_3501_);
lean_dec(v_a_3497_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v_a_3501_);
v___x_3503_ = v___x_3499_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; 
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc_ref(v_e_3478_);
v___x_3511_ = lean_infer_type(v_e_3478_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3901_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3512_, v_a_3481_);
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3901_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3901_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; 
lean_inc(v_a_3507_);
v___x_3518_ = l_Lean_Meta_isTypeApp_x3f(v_a_3507_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3892_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3892_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3892_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
if (lean_obj_tag(v_a_3519_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_3521_);
v_val_3523_ = lean_ctor_get(v_a_3519_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3525_ = v_a_3519_;
v_isShared_3526_ = v_isSharedCheck_3887_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v_a_3519_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3887_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3886_; 
v_fst_3527_ = lean_ctor_get(v_val_3523_, 0);
v_snd_3528_ = lean_ctor_get(v_val_3523_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_val_3523_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3530_ = v_val_3523_;
v_isShared_3531_ = v_isSharedCheck_3886_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_snd_3528_);
lean_inc(v_fst_3527_);
lean_dec(v_val_3523_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3886_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; 
lean_inc(v_a_3514_);
v___x_3532_ = l_Lean_Meta_isTypeApp_x3f(v_a_3514_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3877_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3877_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3877_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
if (lean_obj_tag(v_a_3533_) == 1)
{
lean_object* v_val_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3872_; 
lean_del_object(v___x_3535_);
v_val_3537_ = lean_ctor_get(v_a_3533_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_a_3533_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3539_ = v_a_3533_;
v_isShared_3540_ = v_isSharedCheck_3872_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_val_3537_);
lean_dec(v_a_3533_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3872_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_fst_3541_; lean_object* v_snd_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3871_; 
v_fst_3541_ = lean_ctor_get(v_val_3537_, 0);
v_snd_3542_ = lean_ctor_get(v_val_3537_, 1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_val_3537_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3544_ = v_val_3537_;
v_isShared_3545_ = v_isSharedCheck_3871_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_snd_3542_);
lean_inc(v_fst_3541_);
lean_dec(v_val_3537_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3871_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Meta_saveState___redArg(v_a_3481_, v_a_3483_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
lean_inc(v_fst_3527_);
lean_inc(v_fst_3541_);
v___x_3548_ = l_Lean_Meta_isExprDefEq(v_fst_3541_, v_fst_3527_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3854_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3854_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3854_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_unbox(v_a_3549_);
lean_dec(v_a_3549_);
if (v___x_3553_ == 0)
{
lean_object* v_options_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
lean_dec(v_a_3547_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
v_options_3554_ = lean_ctor_get(v_a_3482_, 2);
v___x_3555_ = l_Lean_Meta_autoLift;
v___x_3556_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3557_ = lean_box(0);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3557_);
v___x_3559_ = v___x_3551_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v___x_3561_; 
lean_del_object(v___x_3551_);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_fst_3541_);
v___x_3561_ = lean_infer_type(v_fst_3541_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
v___x_3563_ = lean_whnf(v_a_3562_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
if (lean_obj_tag(v_a_3564_) == 7)
{
lean_object* v_binderType_3565_; 
v_binderType_3565_ = lean_ctor_get(v_a_3564_, 1);
if (lean_obj_tag(v_binderType_3565_) == 3)
{
lean_object* v_body_3566_; 
v_body_3566_ = lean_ctor_get(v_a_3564_, 2);
if (lean_obj_tag(v_body_3566_) == 3)
{
lean_object* v_u_3567_; lean_object* v_u_3568_; lean_object* v___x_3569_; 
lean_inc_ref(v_body_3566_);
lean_inc_ref(v_binderType_3565_);
lean_dec_ref_known(v_a_3564_, 3);
v_u_3567_ = lean_ctor_get(v_binderType_3565_, 0);
lean_inc(v_u_3567_);
lean_dec_ref_known(v_binderType_3565_, 1);
v_u_3568_ = lean_ctor_get(v_body_3566_, 0);
lean_inc(v_u_3568_);
lean_dec_ref_known(v_body_3566_, 1);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_fst_3527_);
v___x_3569_ = lean_infer_type(v_fst_3527_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
v___x_3571_ = lean_whnf(v_a_3570_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3571_, 1);
if (lean_obj_tag(v_a_3572_) == 7)
{
lean_object* v_binderType_3573_; 
v_binderType_3573_ = lean_ctor_get(v_a_3572_, 1);
if (lean_obj_tag(v_binderType_3573_) == 3)
{
lean_object* v_body_3574_; 
v_body_3574_ = lean_ctor_get(v_a_3572_, 2);
if (lean_obj_tag(v_body_3574_) == 3)
{
lean_object* v_u_3575_; lean_object* v_u_3576_; lean_object* v___x_3577_; 
lean_inc_ref(v_body_3574_);
lean_inc_ref(v_binderType_3573_);
lean_dec_ref_known(v_a_3572_, 3);
v_u_3575_ = lean_ctor_get(v_binderType_3573_, 0);
lean_inc(v_u_3575_);
lean_dec_ref_known(v_binderType_3573_, 1);
v_u_3576_ = lean_ctor_get(v_body_3574_, 0);
lean_inc(v_u_3576_);
lean_dec_ref_known(v_body_3574_, 1);
v___x_3577_ = l_Lean_Meta_decLevel(v_u_3567_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_Meta_decLevel(v_u_3575_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
lean_inc(v_a_3578_);
v___x_3581_ = l_Lean_Meta_isLevelDefEq(v_a_3578_, v_a_3580_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3746_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3746_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3746_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_unbox(v_a_3582_);
lean_dec(v_a_3582_);
if (v___x_3586_ == 1)
{
lean_object* v___x_3587_; 
lean_del_object(v___x_3584_);
v___x_3587_ = l_Lean_Meta_decLevel(v_u_3568_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = l_Lean_Meta_decLevel(v_u_3576_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
v___x_3591_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3592_ = lean_box(0);
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 1);
lean_ctor_set(v___x_3544_, 1, v___x_3592_);
lean_ctor_set(v___x_3544_, 0, v_a_3590_);
v___x_3594_ = v___x_3544_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3590_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set_tag(v___x_3530_, 1);
lean_ctor_set(v___x_3530_, 1, v___x_3594_);
lean_ctor_set(v___x_3530_, 0, v_a_3588_);
v___x_3596_ = v___x_3530_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3588_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_a_3578_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Lean_Expr_const___override(v___x_3591_, v___x_3597_);
v___x_3599_ = lean_unsigned_to_nat(2u);
v___x_3600_ = lean_mk_empty_array_with_capacity(v___x_3599_);
lean_inc(v_fst_3541_);
v___x_3601_ = lean_array_push(v___x_3600_, v_fst_3541_);
lean_inc(v_fst_3527_);
v___x_3602_ = lean_array_push(v___x_3601_, v_fst_3527_);
v___x_3603_ = l_Lean_mkAppN(v___x_3598_, v___x_3602_);
lean_dec_ref(v___x_3602_);
v___x_3604_ = lean_box(0);
v___x_3605_ = l_Lean_Meta_trySynthInstance(v___x_3603_, v___x_3604_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3736_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3736_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3736_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
if (lean_obj_tag(v_a_3606_) == 1)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3608_);
v_a_3610_ = lean_ctor_get(v_a_3606_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v_a_3606_, 1);
lean_inc(v_snd_3542_);
v___x_3611_ = l_Lean_Meta_getDecLevel(v_snd_3542_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3613_ = l_Lean_Meta_getDecLevel(v_a_3514_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
lean_inc(v_a_3507_);
v___x_3615_ = l_Lean_Meta_getDecLevel(v_a_3507_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_a_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3592_);
v___x_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3619_, 0, v_a_3614_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_a_3612_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
lean_inc_ref(v___x_3620_);
v___x_3621_ = l_Lean_mkConst(v___x_3617_, v___x_3620_);
v___x_3622_ = lean_unsigned_to_nat(5u);
v___x_3623_ = lean_mk_empty_array_with_capacity(v___x_3622_);
lean_inc(v_fst_3541_);
v___x_3624_ = lean_array_push(v___x_3623_, v_fst_3541_);
lean_inc(v_fst_3527_);
v___x_3625_ = lean_array_push(v___x_3624_, v_fst_3527_);
lean_inc(v_a_3610_);
v___x_3626_ = lean_array_push(v___x_3625_, v_a_3610_);
lean_inc(v_snd_3542_);
v___x_3627_ = lean_array_push(v___x_3626_, v_snd_3542_);
lean_inc_ref(v_e_3478_);
v___x_3628_ = lean_array_push(v___x_3627_, v_e_3478_);
v___x_3629_ = l_Lean_mkAppN(v___x_3621_, v___x_3628_);
lean_dec_ref(v___x_3628_);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc_ref(v___x_3629_);
v___x_3630_ = lean_infer_type(v___x_3629_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3632_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
lean_inc(v_a_3507_);
v___x_3632_ = l_Lean_Meta_isExprDefEq(v_a_3507_, v_a_3631_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3727_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3727_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3727_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_unbox(v_a_3633_);
lean_dec(v_a_3633_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_del_object(v___x_3635_);
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3539_);
lean_inc(v_fst_3527_);
v___x_3638_ = l_Lean_Meta_isMonad_x3f(v_fst_3527_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3719_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3719_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3719_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
if (lean_obj_tag(v_a_3639_) == 1)
{
lean_object* v_val_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3715_; 
lean_del_object(v___x_3641_);
v_val_3643_ = lean_ctor_get(v_a_3639_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_a_3639_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3645_ = v_a_3639_;
v_isShared_3646_ = v_isSharedCheck_3715_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_val_3643_);
lean_dec(v_a_3639_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3715_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; 
lean_inc(v_snd_3542_);
v___x_3647_ = l_Lean_Meta_getLevel(v_snd_3542_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3649_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3647_, 1);
lean_inc(v_snd_3528_);
v___x_3649_ = l_Lean_Meta_getLevel(v_snd_3528_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3652_ = 0;
v___x_3653_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3654_, 0, v_a_3650_);
lean_ctor_set(v___x_3654_, 1, v___x_3592_);
v___x_3655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_a_3648_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_mkConst(v___x_3653_, v___x_3655_);
v___x_3657_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3658_ = lean_unsigned_to_nat(3u);
v___x_3659_ = lean_mk_empty_array_with_capacity(v___x_3658_);
lean_inc_n(v_snd_3542_, 2);
v___x_3660_ = lean_array_push(v___x_3659_, v_snd_3542_);
v___x_3661_ = lean_array_push(v___x_3660_, v___x_3657_);
lean_inc(v_snd_3528_);
v___x_3662_ = lean_array_push(v___x_3661_, v_snd_3528_);
v___x_3663_ = l_Lean_mkAppN(v___x_3656_, v___x_3662_);
lean_dec_ref(v___x_3662_);
v___x_3664_ = l_Lean_mkForall(v___x_3651_, v___x_3652_, v_snd_3542_, v___x_3663_);
v___x_3665_ = l_Lean_Meta_trySynthInstance(v___x_3664_, v___x_3604_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3711_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3711_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3711_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
if (lean_obj_tag(v_a_3666_) == 1)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_del_object(v___x_3668_);
v_a_3670_ = lean_ctor_get(v_a_3666_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v_a_3666_, 1);
v___x_3671_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3672_ = l_Lean_mkConst(v___x_3671_, v___x_3620_);
v___x_3673_ = lean_unsigned_to_nat(8u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
v___x_3675_ = lean_array_push(v___x_3674_, v_fst_3541_);
v___x_3676_ = lean_array_push(v___x_3675_, v_fst_3527_);
v___x_3677_ = lean_array_push(v___x_3676_, v_snd_3542_);
v___x_3678_ = lean_array_push(v___x_3677_, v_snd_3528_);
v___x_3679_ = lean_array_push(v___x_3678_, v_a_3610_);
v___x_3680_ = lean_array_push(v___x_3679_, v_a_3670_);
v___x_3681_ = lean_array_push(v___x_3680_, v_val_3643_);
v___x_3682_ = lean_array_push(v___x_3681_, v_e_3478_);
v___x_3683_ = l_Lean_mkAppN(v___x_3672_, v___x_3682_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = l_Lean_Meta_expandCoe(v___x_3683_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v_fst_3686_; lean_object* v___x_3687_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v_fst_3686_ = lean_ctor_get(v_a_3685_, 0);
lean_inc_n(v_fst_3686_, 2);
lean_dec(v_a_3685_);
lean_inc(v_a_3483_);
lean_inc_ref(v_a_3482_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
v___x_3687_ = lean_infer_type(v_fst_3686_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = l_Lean_Meta_isExprDefEq(v_a_3507_, v_a_3688_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3704_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3704_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3704_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_unbox(v_a_3690_);
lean_dec(v_a_3690_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3696_; 
lean_dec(v_fst_3686_);
lean_del_object(v___x_3645_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3604_);
v___x_3696_ = v___x_3692_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3604_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
else
{
lean_object* v___x_3699_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v_fst_3686_);
v___x_3699_ = v___x_3645_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_fst_3686_);
v___x_3699_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3701_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3699_);
v___x_3701_ = v___x_3692_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
else
{
lean_object* v_a_3705_; 
lean_dec(v_fst_3686_);
lean_del_object(v___x_3645_);
v_a_3705_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3689_, 1);
v_a_3492_ = v_a_3705_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3706_; 
lean_dec(v_fst_3686_);
lean_del_object(v___x_3645_);
lean_dec(v_a_3507_);
v_a_3706_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3687_, 1);
v_a_3492_ = v_a_3706_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3707_; 
lean_del_object(v___x_3645_);
lean_dec(v_a_3507_);
v_a_3707_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3684_, 1);
v_a_3492_ = v_a_3707_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3709_; 
lean_dec(v_a_3666_);
lean_del_object(v___x_3645_);
lean_dec(v_val_3643_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3604_);
v___x_3709_ = v___x_3668_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3604_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; 
lean_del_object(v___x_3645_);
lean_dec(v_val_3643_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3712_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3665_, 1);
v_a_3492_ = v_a_3712_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3713_; 
lean_dec(v_a_3648_);
lean_del_object(v___x_3645_);
lean_dec(v_val_3643_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3713_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3649_, 1);
v_a_3492_ = v_a_3713_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3714_; 
lean_del_object(v___x_3645_);
lean_dec(v_val_3643_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3714_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3647_, 1);
v_a_3492_ = v_a_3714_;
goto v___jp_3491_;
}
}
}
else
{
lean_object* v___x_3717_; 
lean_dec(v_a_3639_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3604_);
v___x_3717_ = v___x_3641_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3604_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_a_3720_; 
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3720_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3638_, 1);
v_a_3492_ = v_a_3720_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3722_; 
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3629_);
v___x_3722_ = v___x_3539_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3629_);
v___x_3722_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3724_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3722_);
v___x_3724_ = v___x_3635_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
else
{
lean_object* v_a_3728_; 
lean_dec_ref(v___x_3629_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3728_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3632_, 1);
v_a_3492_ = v_a_3728_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3729_; 
lean_dec_ref(v___x_3629_);
lean_dec_ref_known(v___x_3620_, 2);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3729_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3630_, 1);
v_a_3492_ = v_a_3729_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3730_; 
lean_dec(v_a_3614_);
lean_dec(v_a_3612_);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3730_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3615_, 1);
v_a_3492_ = v_a_3730_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3731_; 
lean_dec(v_a_3612_);
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3731_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3613_, 1);
v_a_3492_ = v_a_3731_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3732_; 
lean_dec(v_a_3610_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3732_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3611_, 1);
v_a_3492_ = v_a_3732_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3734_; 
lean_dec(v_a_3606_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3604_);
v___x_3734_ = v___x_3608_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3604_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; 
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3737_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3605_, 1);
v_a_3492_ = v_a_3737_;
goto v___jp_3491_;
}
}
}
}
else
{
lean_object* v_a_3740_; 
lean_dec(v_a_3588_);
lean_dec(v_a_3578_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3740_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3589_, 1);
v_a_3492_ = v_a_3740_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3741_; 
lean_dec(v_a_3578_);
lean_dec(v_u_3576_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3741_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3587_, 1);
v_a_3492_ = v_a_3741_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_dec(v_a_3578_);
lean_dec(v_u_3576_);
lean_dec(v_u_3568_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3742_ = lean_box(0);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3742_);
v___x_3744_ = v___x_3584_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; 
lean_dec(v_a_3578_);
lean_dec(v_u_3576_);
lean_dec(v_u_3568_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3747_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3581_, 1);
v_a_3492_ = v_a_3747_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3748_; 
lean_dec(v_a_3578_);
lean_dec(v_u_3576_);
lean_dec(v_u_3568_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3748_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3579_, 1);
v_a_3492_ = v_a_3748_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3749_; 
lean_dec(v_u_3576_);
lean_dec(v_u_3575_);
lean_dec(v_u_3568_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3749_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3577_, 1);
v_a_3492_ = v_a_3749_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3750_; 
lean_dec(v_u_3568_);
lean_dec(v_u_3567_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3750_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3572_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec_ref_known(v_a_3572_, 3);
v___y_3496_ = v___x_3750_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3751_; 
lean_dec(v_u_3568_);
lean_dec(v_u_3567_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3751_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3572_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec_ref_known(v_a_3572_, 3);
v___y_3496_ = v___x_3751_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3752_; 
lean_dec(v_u_3568_);
lean_dec(v_u_3567_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3752_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3572_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3572_);
v___y_3496_ = v___x_3752_;
goto v___jp_3495_;
}
}
else
{
lean_object* v_a_3753_; 
lean_dec(v_u_3568_);
lean_dec(v_u_3567_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3753_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3571_, 1);
v_a_3492_ = v_a_3753_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3754_; 
lean_dec(v_u_3568_);
lean_dec(v_u_3567_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3754_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3569_, 1);
v_a_3492_ = v_a_3754_;
goto v___jp_3491_;
}
}
else
{
lean_object* v___x_3755_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3755_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3564_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec_ref_known(v_a_3564_, 3);
v___y_3496_ = v___x_3755_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3756_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3756_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3564_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec_ref_known(v_a_3564_, 3);
v___y_3496_ = v___x_3756_;
goto v___jp_3495_;
}
}
else
{
lean_object* v___x_3757_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3757_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3564_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3564_);
v___y_3496_ = v___x_3757_;
goto v___jp_3495_;
}
}
else
{
lean_object* v_a_3758_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3758_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3563_, 1);
v_a_3492_ = v_a_3758_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3759_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3759_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3561_, 1);
v_a_3492_ = v_a_3759_;
goto v___jp_3491_;
}
}
}
else
{
lean_object* v___x_3760_; 
lean_del_object(v___x_3551_);
lean_del_object(v___x_3544_);
lean_del_object(v___x_3530_);
lean_dec(v_a_3514_);
lean_dec(v_a_3507_);
v___x_3760_ = l_Lean_Meta_isMonad_x3f(v_fst_3527_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3853_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3853_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3853_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
if (lean_obj_tag(v_a_3761_) == 1)
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v_fst_3541_);
v___x_3767_ = v___x_3539_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_fst_3541_);
v___x_3767_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3769_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_snd_3542_);
v___x_3769_ = v___x_3525_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_snd_3542_);
v___x_3769_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 1);
lean_ctor_set(v___x_3516_, 0, v_snd_3528_);
v___x_3771_ = v___x_3516_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_snd_3528_);
v___x_3771_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___y_3774_; uint8_t v___y_3775_; lean_object* v_a_3797_; lean_object* v___x_3801_; 
v___x_3772_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 1);
lean_ctor_set(v___x_3509_, 0, v_e_3478_);
v___x_3801_ = v___x_3509_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_e_3478_);
v___x_3801_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3800_;
}
v___jp_3773_:
{
if (v___y_3775_ == 0)
{
lean_object* v___x_3776_; 
lean_dec_ref(v___y_3774_);
lean_del_object(v___x_3763_);
v___x_3776_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3547_, v_a_3481_, v_a_3483_);
lean_dec(v_a_3547_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; 
v_unused_3784_ = lean_ctor_get(v___x_3776_, 0);
lean_dec(v_unused_3784_);
v___x_3778_ = v___x_3776_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_dec(v___x_3776_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3772_);
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3772_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_a_3785_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3776_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3776_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v___x_3794_; 
lean_dec(v_a_3547_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 1);
lean_ctor_set(v___x_3763_, 0, v___y_3774_);
v___x_3794_ = v___x_3763_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___y_3774_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
v___jp_3796_:
{
uint8_t v___x_3798_; 
v___x_3798_ = l_Lean_Exception_isInterrupt(v_a_3797_);
if (v___x_3798_ == 0)
{
uint8_t v___x_3799_; 
lean_inc_ref(v_a_3797_);
v___x_3799_ = l_Lean_Exception_isRuntime(v_a_3797_);
v___y_3774_ = v_a_3797_;
v___y_3775_ = v___x_3799_;
goto v___jp_3773_;
}
else
{
v___y_3774_ = v_a_3797_;
v___y_3775_ = v___x_3798_;
goto v___jp_3773_;
}
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3802_ = lean_unsigned_to_nat(6u);
v___x_3803_ = lean_mk_empty_array_with_capacity(v___x_3802_);
v___x_3804_ = lean_array_push(v___x_3803_, v___x_3767_);
v___x_3805_ = lean_array_push(v___x_3804_, v___x_3769_);
v___x_3806_ = lean_array_push(v___x_3805_, v___x_3771_);
v___x_3807_ = lean_array_push(v___x_3806_, v___x_3772_);
v___x_3808_ = lean_array_push(v___x_3807_, v_a_3761_);
v___x_3809_ = lean_array_push(v___x_3808_, v___x_3801_);
v___x_3810_ = l_Lean_Meta_mkAppOptM(v___x_3765_, v___x_3809_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3829_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3829_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3829_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Meta_expandCoe(v_a_3811_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3827_; 
lean_del_object(v___x_3763_);
lean_dec(v_a_3547_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_fst_3820_; lean_object* v___x_3822_; 
v_fst_3820_ = lean_ctor_get(v_a_3816_, 0);
lean_inc(v_fst_3820_);
lean_dec(v_a_3816_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 1);
lean_ctor_set(v___x_3813_, 0, v_fst_3820_);
v___x_3822_ = v___x_3813_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_fst_3820_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3824_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3822_);
v___x_3824_ = v___x_3818_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v_a_3828_; 
lean_del_object(v___x_3813_);
v_a_3828_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3815_, 1);
v_a_3797_ = v_a_3828_;
goto v___jp_3796_;
}
}
}
else
{
lean_object* v_a_3830_; 
v_a_3830_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3810_, 1);
v_a_3797_ = v_a_3830_;
goto v___jp_3796_;
}
}
}
}
}
}
else
{
lean_object* v___x_3835_; 
lean_del_object(v___x_3763_);
lean_dec(v_a_3761_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_dec_ref(v_e_3478_);
v___x_3835_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3547_, v_a_3481_, v_a_3483_);
lean_dec(v_a_3547_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3843_; 
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; 
v_unused_3844_ = lean_ctor_get(v___x_3835_, 0);
lean_dec(v_unused_3844_);
v___x_3837_ = v___x_3835_;
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
else
{
lean_dec(v___x_3835_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3839_ = lean_box(0);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3839_);
v___x_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
v_a_3845_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3835_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3835_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3547_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_snd_3528_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_dec_ref(v_e_3478_);
return v___x_3760_;
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3547_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3855_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3548_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3548_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_fst_3541_);
lean_del_object(v___x_3539_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3863_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3546_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3546_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
lean_dec(v_a_3533_);
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3873_ = lean_box(0);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3873_);
v___x_3875_ = v___x_3535_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3530_);
lean_dec(v_snd_3528_);
lean_dec(v_fst_3527_);
lean_del_object(v___x_3525_);
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3878_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3532_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3532_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3890_; 
lean_dec(v_a_3519_);
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v___x_3888_ = lean_box(0);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3888_);
v___x_3890_ = v___x_3521_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3893_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3518_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3518_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3509_);
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3478_);
v_a_3902_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3511_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3511_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3911_, lean_object* v_expectedType_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3911_, v_expectedType_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3919_, lean_object* v_expectedType_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3926_; 
lean_inc_ref(v_expectedType_3920_);
lean_inc_ref(v_expr_3919_);
v___x_3926_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3919_, v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_4006_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3929_ = v___x_3926_;
v_isShared_3930_ = v_isSharedCheck_4006_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_4006_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
if (lean_obj_tag(v_a_3927_) == 1)
{
lean_object* v_val_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_val_3931_ = lean_ctor_get(v_a_3927_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_a_3927_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3933_ = v_a_3927_;
v_isShared_3934_ = v_isSharedCheck_3943_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_val_3931_);
lean_dec(v_a_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3943_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3935_ = lean_box(0);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v_val_3931_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3936_);
v___x_3938_ = v___x_3933_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3938_);
v___x_3940_ = v___x_3929_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
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
else
{
lean_object* v___x_3944_; 
lean_del_object(v___x_3929_);
lean_dec(v_a_3927_);
lean_inc_ref(v_expectedType_3920_);
v___x_3944_ = l_Lean_Meta_whnfR(v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; uint8_t v___x_3946_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
v___x_3946_ = l_Lean_Expr_isForall(v_a_3945_);
lean_dec(v_a_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3919_, v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; 
lean_inc_ref(v_expr_3919_);
v___x_3948_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3919_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_a_3949_);
lean_dec_ref_known(v___x_3948_, 1);
if (lean_obj_tag(v_a_3949_) == 1)
{
lean_object* v_val_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3988_; 
v_val_3950_ = lean_ctor_get(v_a_3949_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_a_3949_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3952_ = v_a_3949_;
v_isShared_3953_ = v_isSharedCheck_3988_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_val_3950_);
lean_dec(v_a_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3988_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; 
lean_inc(v_a_3924_);
lean_inc_ref(v_a_3923_);
lean_inc(v_a_3922_);
lean_inc_ref(v_a_3921_);
lean_inc(v_val_3950_);
v___x_3954_ = lean_infer_type(v_val_3950_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
lean_inc_ref(v_expectedType_3920_);
v___x_3956_ = l_Lean_Meta_isExprDefEq(v_a_3955_, v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3971_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3971_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3971_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
uint8_t v___x_3961_; 
v___x_3961_ = lean_unbox(v_a_3957_);
lean_dec(v_a_3957_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; 
lean_del_object(v___x_3959_);
lean_del_object(v___x_3952_);
lean_dec(v_val_3950_);
v___x_3962_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3919_, v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
return v___x_3962_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_val_3950_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3964_);
v___x_3966_ = v___x_3952_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3968_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3966_);
v___x_3968_ = v___x_3959_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_del_object(v___x_3952_);
lean_dec(v_val_3950_);
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_a_3972_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3956_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3956_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_del_object(v___x_3952_);
lean_dec(v_val_3950_);
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_a_3980_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3954_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3954_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
else
{
lean_object* v___x_3989_; 
lean_dec(v_a_3949_);
v___x_3989_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3919_, v_expectedType_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
return v___x_3989_;
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_a_3990_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3948_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3948_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_a_3998_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3944_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3944_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v_expectedType_3920_);
lean_dec_ref(v_expr_3919_);
v_a_4007_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3926_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3926_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_4015_, lean_object* v_expectedType_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_4015_, v_expectedType_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_4023_, lean_object* v_expectedType_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_4023_, v_expectedType_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4055_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4055_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
switch(lean_obj_tag(v_a_4031_))
{
case 0:
{
lean_object* v___x_4035_; lean_object* v___x_4037_; 
v___x_4035_ = lean_box(0);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4035_);
v___x_4037_ = v___x_4033_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
case 1:
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4050_; 
v_a_4039_ = lean_ctor_get(v_a_4031_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_a_4031_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4041_ = v_a_4031_;
v_isShared_4042_ = v_isSharedCheck_4050_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v_a_4031_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4050_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_fst_4043_; lean_object* v___x_4045_; 
v_fst_4043_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_fst_4043_);
lean_dec(v_a_4039_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_fst_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_fst_4043_);
v___x_4045_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4047_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4045_);
v___x_4047_ = v___x_4033_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
default: 
{
lean_object* v___x_4051_; lean_object* v___x_4053_; 
v___x_4051_ = lean_box(2);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4051_);
v___x_4053_ = v___x_4033_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v_a_4056_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4030_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4030_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_4064_, lean_object* v_expectedType_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_Meta_coerce_x3f(v_expr_4064_, v_expectedType_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
return v_res_4071_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Coe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_coeDeclAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_coeDeclAttr);
lean_dec_ref(res);
res = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_autoLift = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_autoLift);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Coe(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Coe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Coe(builtin);
}
#ifdef __cplusplus
}
#endif
