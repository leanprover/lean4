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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_indirectModUseExt;
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_178_; lean_object* v_env_179_; lean_object* v___x_180_; lean_object* v_toCold_181_; lean_object* v_mctx_182_; lean_object* v_lctx_183_; lean_object* v_options_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_st_ref_get(v___y_174_);
v_toCold_181_ = lean_ctor_get(v___y_175_, 0);
v_mctx_182_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_mctx_182_);
lean_dec(v___x_180_);
v_lctx_183_ = lean_ctor_get(v___y_173_, 2);
v_options_184_ = lean_ctor_get(v_toCold_181_, 2);
lean_inc_ref(v_options_184_);
lean_inc_ref(v_lctx_183_);
v___x_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_185_, 0, v_env_179_);
lean_ctor_set(v___x_185_, 1, v_mctx_182_);
lean_ctor_set(v___x_185_, 2, v_lctx_183_);
lean_ctor_set(v___x_185_, 3, v_options_184_);
v___x_186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_msgData_172_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_195_; double v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_float_of_nat(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_200_, lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_255_; 
v_ref_208_ = lean_ctor_get(v___y_205_, 2);
v___x_209_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_201_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_255_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_255_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_255_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_traceState_215_; lean_object* v_env_216_; lean_object* v_nextMacroScope_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_cache_220_; lean_object* v_messages_221_; lean_object* v_infoState_222_; lean_object* v_snapshotTasks_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_254_; 
v___x_214_ = lean_st_ref_take(v___y_206_);
v_traceState_215_ = lean_ctor_get(v___x_214_, 4);
v_env_216_ = lean_ctor_get(v___x_214_, 0);
v_nextMacroScope_217_ = lean_ctor_get(v___x_214_, 1);
v_ngen_218_ = lean_ctor_get(v___x_214_, 2);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_214_, 3);
v_cache_220_ = lean_ctor_get(v___x_214_, 5);
v_messages_221_ = lean_ctor_get(v___x_214_, 6);
v_infoState_222_ = lean_ctor_get(v___x_214_, 7);
v_snapshotTasks_223_ = lean_ctor_get(v___x_214_, 8);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_254_ == 0)
{
v___x_225_ = v___x_214_;
v_isShared_226_ = v_isSharedCheck_254_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snapshotTasks_223_);
lean_inc(v_infoState_222_);
lean_inc(v_messages_221_);
lean_inc(v_cache_220_);
lean_inc(v_traceState_215_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_env_216_);
lean_dec(v___x_214_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_254_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint64_t v_tid_227_; lean_object* v_traces_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_253_; 
v_tid_227_ = lean_ctor_get_uint64(v_traceState_215_, sizeof(void*)*1);
v_traces_228_ = lean_ctor_get(v_traceState_215_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_traceState_215_);
if (v_isSharedCheck_253_ == 0)
{
v___x_230_ = v_traceState_215_;
v_isShared_231_ = v_isSharedCheck_253_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_traces_228_);
lean_dec(v_traceState_215_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_253_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; double v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_234_ = 0;
v___x_235_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_236_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_236_, 0, v_cls_200_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3, v___x_233_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3 + 8, v___x_233_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 16, v___x_234_);
v___x_237_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_238_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v_a_210_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_inc(v_ref_208_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_208_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_Lean_PersistentArray_push___redArg(v_traces_228_, v___x_239_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_240_);
v___x_242_ = v___x_230_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_240_);
lean_ctor_set_uint64(v_reuseFailAlloc_252_, sizeof(void*)*1, v_tid_227_);
v___x_242_ = v_reuseFailAlloc_252_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 4, v___x_242_);
v___x_244_ = v___x_225_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_env_216_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_251_, 5, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_251_, 6, v_messages_221_);
lean_ctor_set(v_reuseFailAlloc_251_, 7, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_251_, 8, v_snapshotTasks_223_);
v___x_244_ = v_reuseFailAlloc_251_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = lean_st_ref_put(v___y_206_, v___x_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_202_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_247_);
v___x_249_ = v___x_212_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_256_, v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_265_, lean_object* v_i_266_, lean_object* v_k_267_){
_start:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_array_get_size(v_keys_265_);
v___x_269_ = lean_nat_dec_lt(v_i_266_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v_i_266_);
return v___x_269_;
}
else
{
lean_object* v_k_x27_270_; uint8_t v___x_271_; 
v_k_x27_270_ = lean_array_fget_borrowed(v_keys_265_, v_i_266_);
v___x_271_ = l_Lean_instBEqExtraModUse_beq(v_k_267_, v_k_x27_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_i_266_, v___x_272_);
lean_dec(v_i_266_);
v_i_266_ = v___x_273_;
goto _start;
}
else
{
lean_dec(v_i_266_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_275_, lean_object* v_i_276_, lean_object* v_k_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_275_, v_i_276_, v_k_277_);
lean_dec_ref(v_k_277_);
lean_dec_ref(v_keys_275_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_280_, size_t v_x_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_es_283_; lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v_j_287_; lean_object* v___x_288_; 
v_es_283_ = lean_ctor_get(v_x_280_, 0);
v___x_284_ = lean_box(2);
v___x_285_ = ((size_t)31ULL);
v___x_286_ = lean_usize_land(v_x_281_, v___x_285_);
v_j_287_ = lean_usize_to_nat(v___x_286_);
v___x_288_ = lean_array_get_borrowed(v___x_284_, v_es_283_, v_j_287_);
lean_dec(v_j_287_);
switch(lean_obj_tag(v___x_288_))
{
case 0:
{
lean_object* v_key_289_; uint8_t v___x_290_; 
v_key_289_ = lean_ctor_get(v___x_288_, 0);
v___x_290_ = l_Lean_instBEqExtraModUse_beq(v_x_282_, v_key_289_);
return v___x_290_;
}
case 1:
{
lean_object* v_node_291_; size_t v___x_292_; size_t v___x_293_; 
v_node_291_ = lean_ctor_get(v___x_288_, 0);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_usize_shift_right(v_x_281_, v___x_292_);
v_x_280_ = v_node_291_;
v_x_281_ = v___x_293_;
goto _start;
}
default: 
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
}
else
{
lean_object* v_ks_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_ks_296_ = lean_ctor_get(v_x_280_, 0);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_296_, v___x_297_, v_x_282_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
size_t v_x_36072__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_x_36072__boxed_302_ = lean_unbox_usize(v_x_300_);
lean_dec(v_x_300_);
v_res_303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_299_, v_x_36072__boxed_302_, v_x_301_);
lean_dec_ref(v_x_301_);
lean_dec_ref(v_x_299_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint64_t v___x_307_; size_t v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_instHashableExtraModUse_hash(v_x_306_);
v___x_308_ = lean_uint64_to_usize(v___x_307_);
v___x_309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_305_, v___x_308_, v_x_306_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_310_, v_x_311_);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1));
v___x_317_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0));
v___x_318_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_319_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_325_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_ctor_set(v___x_325_, 3, v___x_324_);
lean_ctor_set(v___x_325_, 4, v___x_324_);
lean_ctor_set(v___x_325_, 5, v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11));
v___x_334_ = l_Lean_stringToMessageData(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_cls_340_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_341_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_342_ = l_Lean_Name_append(v___x_341_, v_cls_340_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_353_, uint8_t v_isMeta_354_, lean_object* v_hint_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_env_363_; uint8_t v_isExporting_364_; lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v_entry_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_362_ = lean_st_ref_get(v___y_360_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
v_isExporting_364_ = lean_ctor_get_uint8(v_env_363_, sizeof(void*)*8);
lean_dec_ref(v_env_363_);
v___x_365_ = lean_st_ref_get(v___y_360_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
lean_inc(v_mod_353_);
v_entry_368_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_368_, 0, v_mod_353_);
lean_ctor_set_uint8(v_entry_368_, sizeof(void*)*1, v_isExporting_364_);
lean_ctor_set_uint8(v_entry_368_, sizeof(void*)*1 + 1, v_isMeta_354_);
v___x_369_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_370_ = lean_box(1);
v___x_371_ = lean_box(0);
v___x_416_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_367_, v___x_369_, v_env_366_, v___x_370_, v___x_371_);
v___x_417_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_416_, v_entry_368_);
lean_dec(v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v_toCold_418_; lean_object* v_options_419_; uint8_t v_hasTrace_420_; 
v_toCold_418_ = lean_ctor_get(v___y_359_, 0);
v_options_419_ = lean_ctor_get(v_toCold_418_, 2);
v_hasTrace_420_ = lean_ctor_get_uint8(v_options_419_, sizeof(void*)*1);
if (v_hasTrace_420_ == 0)
{
lean_dec(v_hint_355_);
lean_dec(v_mod_353_);
v___y_373_ = v___y_356_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_360_;
goto v___jp_372_;
}
else
{
lean_object* v_inheritedTraceOptions_421_; lean_object* v_cls_422_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_inheritedTraceOptions_421_ = lean_ctor_get(v_toCold_418_, 11);
v_cls_422_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_421_, v_options_419_, v___x_444_);
if (v___x_445_ == 0)
{
lean_dec(v_hint_355_);
lean_dec(v_mod_353_);
v___y_373_ = v___y_356_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_360_;
goto v___jp_372_;
}
else
{
lean_object* v___x_446_; lean_object* v___y_448_; 
v___x_446_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_364_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_448_ = v___x_455_;
goto v___jp_447_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_448_ = v___x_456_;
goto v___jp_447_;
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref(v___y_448_);
v___x_449_ = l_Lean_stringToMessageData(v___y_448_);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_446_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
if (v_isMeta_354_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_431_ = v___x_452_;
v___y_432_ = v___x_453_;
goto v___jp_430_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_431_ = v___x_452_;
v___y_432_ = v___x_454_;
goto v___jp_430_;
}
}
}
v___jp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___y_424_);
lean_ctor_set(v___x_426_, 1, v___y_425_);
v___x_427_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_422_, v___x_426_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_snd_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v_snd_429_ = lean_ctor_get(v_a_428_, 1);
lean_inc(v_snd_429_);
lean_dec(v_a_428_);
v___y_373_ = v_snd_429_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_360_;
goto v___jp_372_;
}
else
{
lean_dec_ref_known(v_entry_368_, 1);
return v___x_427_;
}
}
v___jp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
lean_inc_ref(v___y_432_);
v___x_433_ = l_Lean_stringToMessageData(v___y_432_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___y_431_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_MessageData_ofName(v_mod_353_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_Name_isAnonymous(v_hint_355_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_441_ = l_Lean_MessageData_ofName(v_hint_355_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___y_424_ = v___x_438_;
v___y_425_ = v___x_442_;
goto v___jp_423_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v_hint_355_);
v___x_443_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_424_ = v___x_438_;
v___y_425_ = v___x_443_;
goto v___jp_423_;
}
}
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref_known(v_entry_368_, 1);
lean_dec(v_hint_355_);
lean_dec(v_mod_353_);
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___y_356_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
v___jp_372_:
{
lean_object* v___x_376_; lean_object* v_toEnvExtension_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_traceState_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_414_; 
v___x_376_ = lean_st_ref_take(v___y_375_);
v_toEnvExtension_377_ = lean_ctor_get(v___x_369_, 0);
v_env_378_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_376_, 1);
v_ngen_380_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_376_, 3);
v_traceState_382_ = lean_ctor_get(v___x_376_, 4);
v_messages_383_ = lean_ctor_get(v___x_376_, 6);
v_infoState_384_ = lean_ctor_get(v___x_376_, 7);
v_snapshotTasks_385_ = lean_ctor_get(v___x_376_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_376_, 5);
lean_dec(v_unused_415_);
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_414_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_414_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_asyncMode_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_asyncMode_389_ = lean_ctor_get(v_toEnvExtension_377_, 2);
v___x_390_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_369_, v_env_378_, v_entry_368_, v_asyncMode_389_, v___x_371_);
v___x_391_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 5, v___x_391_);
lean_ctor_set(v___x_387_, 0, v___x_390_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_traceState_382_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_snapshotTasks_385_);
v___x_393_ = v_reuseFailAlloc_413_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_mctx_396_; lean_object* v_zetaDeltaFVarIds_397_; lean_object* v_postponed_398_; lean_object* v_diag_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_411_; 
v___x_394_ = lean_st_ref_put(v___y_375_, v___x_393_);
v___x_395_ = lean_st_ref_take(v___y_374_);
v_mctx_396_ = lean_ctor_get(v___x_395_, 0);
v_zetaDeltaFVarIds_397_ = lean_ctor_get(v___x_395_, 2);
v_postponed_398_ = lean_ctor_get(v___x_395_, 3);
v_diag_399_ = lean_ctor_get(v___x_395_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_395_, 1);
lean_dec(v_unused_412_);
v___x_401_ = v___x_395_;
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_diag_399_);
lean_inc(v_postponed_398_);
lean_inc(v_zetaDeltaFVarIds_397_);
lean_inc(v_mctx_396_);
lean_dec(v___x_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_mctx_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_zetaDeltaFVarIds_397_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_postponed_398_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_diag_399_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_st_ref_put(v___y_374_, v___x_405_);
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___y_373_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_460_, lean_object* v_isMeta_461_, lean_object* v_hint_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_isMeta_boxed_469_; lean_object* v_res_470_; 
v_isMeta_boxed_469_ = lean_unbox(v_isMeta_461_);
v_res_470_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_460_, v_isMeta_boxed_469_, v_hint_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v_key_474_; lean_object* v_value_475_; lean_object* v_tail_476_; uint8_t v___x_477_; 
v_key_474_ = lean_ctor_get(v_x_472_, 0);
v_value_475_ = lean_ctor_get(v_x_472_, 1);
v_tail_476_ = lean_ctor_get(v_x_472_, 2);
v___x_477_ = lean_name_eq(v_key_474_, v_a_471_);
if (v___x_477_ == 0)
{
v_x_472_ = v_tail_476_;
goto _start;
}
else
{
lean_object* v___x_479_; 
lean_inc(v_value_475_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_value_475_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_buckets_485_; lean_object* v___x_486_; uint64_t v___y_488_; 
v_buckets_485_ = lean_ctor_get(v_m_483_, 1);
v___x_486_ = lean_array_get_size(v_buckets_485_);
if (lean_obj_tag(v_a_484_) == 0)
{
uint64_t v___x_502_; 
v___x_502_ = 1723ULL;
v___y_488_ = v___x_502_;
goto v___jp_487_;
}
else
{
uint64_t v_hash_503_; 
v_hash_503_ = lean_ctor_get_uint64(v_a_484_, sizeof(void*)*2);
v___y_488_ = v_hash_503_;
goto v___jp_487_;
}
v___jp_487_:
{
uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v_fold_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_489_ = 32ULL;
v___x_490_ = lean_uint64_shift_right(v___y_488_, v___x_489_);
v_fold_491_ = lean_uint64_xor(v___y_488_, v___x_490_);
v___x_492_ = 16ULL;
v___x_493_ = lean_uint64_shift_right(v_fold_491_, v___x_492_);
v___x_494_ = lean_uint64_xor(v_fold_491_, v___x_493_);
v___x_495_ = lean_uint64_to_usize(v___x_494_);
v___x_496_ = lean_usize_of_nat(v___x_486_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_sub(v___x_496_, v___x_497_);
v___x_499_ = lean_usize_land(v___x_495_, v___x_498_);
v___x_500_ = lean_array_uget_borrowed(v_buckets_485_, v___x_499_);
v___x_501_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_484_, v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_m_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_507_, lean_object* v_declName_508_, lean_object* v_as_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_declName_508_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_b_512_);
lean_ctor_set(v___x_520_, 1, v___y_513_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v_modules_523_; lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v_toImport_527_; lean_object* v_module_528_; uint8_t v___x_529_; lean_object* v___x_530_; 
v___x_522_ = l_Lean_Environment_header(v___x_507_);
v_modules_523_ = lean_ctor_get(v___x_522_, 3);
lean_inc_ref(v_modules_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_525_ = lean_array_uget_borrowed(v_as_509_, v_i_511_);
v___x_526_ = lean_array_get(v___x_524_, v_modules_523_, v_a_525_);
lean_dec_ref(v_modules_523_);
v_toImport_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_toImport_527_);
lean_dec(v___x_526_);
v_module_528_ = lean_ctor_get(v_toImport_527_, 0);
lean_inc(v_module_528_);
lean_dec_ref(v_toImport_527_);
v___x_529_ = 0;
lean_inc(v_declName_508_);
v___x_530_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_528_, v___x_529_, v_declName_508_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v_snd_532_; lean_object* v___x_533_; size_t v___x_534_; size_t v___x_535_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v_snd_532_ = lean_ctor_get(v_a_531_, 1);
lean_inc(v_snd_532_);
lean_dec(v_a_531_);
v___x_533_ = lean_box(0);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_511_, v___x_534_);
v_i_511_ = v___x_535_;
v_b_512_ = v___x_533_;
v___y_513_ = v_snd_532_;
goto _start;
}
else
{
lean_dec(v_declName_508_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_537_, lean_object* v_declName_538_, lean_object* v_as_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_550_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_537_, v_declName_538_, v_as_539_, v_sz_boxed_549_, v_i_boxed_550_, v_b_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_as_539_);
lean_dec_ref(v___x_537_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_555_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_556_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_555_, v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_559_, uint8_t v_isMeta_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_env_572_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___x_597_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_572_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_567_);
v___x_597_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_572_, v_declName_559_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_dec_ref(v_env_572_);
lean_dec(v_declName_559_);
goto v___jp_568_;
}
else
{
lean_object* v_val_598_; lean_object* v___x_599_; lean_object* v_modules_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_val_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_Environment_header(v_env_572_);
v_modules_600_ = lean_ctor_get(v___x_599_, 3);
lean_inc_ref(v_modules_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_array_get_size(v_modules_600_);
v___x_602_ = lean_nat_dec_lt(v_val_598_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec_ref(v_modules_600_);
lean_dec(v_val_598_);
lean_dec_ref(v_env_572_);
lean_dec(v_declName_559_);
goto v___jp_568_;
}
else
{
lean_object* v___x_603_; lean_object* v_env_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___y_608_; 
v___x_603_ = lean_st_ref_get(v___y_565_);
v_env_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc_ref(v_env_604_);
lean_dec(v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_606_ = lean_array_fget(v_modules_600_, v_val_598_);
lean_dec(v_val_598_);
lean_dec_ref(v_modules_600_);
if (v_isMeta_560_ == 0)
{
lean_dec_ref(v_env_604_);
v___y_608_ = v_isMeta_560_;
goto v___jp_607_;
}
else
{
uint8_t v___x_621_; 
lean_inc(v_declName_559_);
v___x_621_ = l_Lean_isMarkedMeta(v_env_604_, v_declName_559_);
if (v___x_621_ == 0)
{
v___y_608_ = v_isMeta_560_;
goto v___jp_607_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
v___y_608_ = v___x_622_;
goto v___jp_607_;
}
}
v___jp_607_:
{
lean_object* v_toImport_609_; lean_object* v_module_610_; lean_object* v___x_611_; 
v_toImport_609_ = lean_ctor_get(v___x_606_, 0);
lean_inc_ref(v_toImport_609_);
lean_dec(v___x_606_);
v_module_610_ = lean_ctor_get(v_toImport_609_, 0);
lean_inc(v_module_610_);
lean_dec_ref(v_toImport_609_);
lean_inc(v_declName_559_);
v___x_611_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_610_, v___y_608_, v_declName_559_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v_snd_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v_snd_613_ = lean_ctor_get(v_a_612_, 1);
lean_inc(v_snd_613_);
lean_dec(v_a_612_);
v___x_614_ = l_Lean_indirectModUseExt;
v___x_615_ = lean_box(1);
v___x_616_ = lean_box(0);
lean_inc_ref(v_env_572_);
v___x_617_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_605_, v___x_614_, v_env_572_, v___x_615_, v___x_616_);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_617_, v_declName_559_);
lean_dec(v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_574_ = v_snd_613_;
v___y_575_ = v___x_619_;
goto v___jp_573_;
}
else
{
lean_object* v_val_620_; 
v_val_620_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v___x_618_, 1);
v___y_574_ = v_snd_613_;
v___y_575_ = v_val_620_;
goto v___jp_573_;
}
}
else
{
lean_dec_ref(v_env_572_);
lean_dec(v_declName_559_);
return v___x_611_;
}
}
}
}
v___jp_568_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___y_561_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
v___jp_573_:
{
lean_object* v___x_576_; size_t v_sz_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_box(0);
v_sz_577_ = lean_array_size(v___y_575_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_572_, v_declName_559_, v___y_575_, v_sz_577_, v___x_578_, v___x_576_, v___y_574_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v_env_572_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_596_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_596_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_596_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_596_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_594_; 
v_snd_584_ = lean_ctor_get(v_a_580_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_580_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_a_580_, 0);
lean_dec(v_unused_595_);
v___x_586_ = v_a_580_;
v_isShared_587_ = v_isSharedCheck_594_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_dec(v_a_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_594_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_576_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_snd_584_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_589_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_623_, lean_object* v_isMeta_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
uint8_t v_isMeta_boxed_631_; lean_object* v_res_632_; 
v_isMeta_boxed_631_ = lean_unbox(v_isMeta_624_);
v_res_632_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_623_, v_isMeta_boxed_631_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___y_648_; lean_object* v_f_652_; uint8_t v___x_653_; 
v_f_652_ = l_Lean_Expr_getAppFn(v_e_640_);
v___x_653_ = l_Lean_Expr_isConst(v_f_652_);
if (v___x_653_ == 0)
{
lean_dec_ref(v_f_652_);
lean_dec_ref(v_e_640_);
v___y_648_ = v___y_641_;
goto v___jp_647_;
}
else
{
lean_object* v___x_654_; lean_object* v_env_655_; lean_object* v_declName_656_; uint8_t v___x_657_; 
v___x_654_ = lean_st_ref_get(v___y_645_);
v_env_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_env_655_);
lean_dec(v___x_654_);
v_declName_656_ = l_Lean_Expr_constName_x21(v_f_652_);
lean_dec_ref(v_f_652_);
lean_inc(v_declName_656_);
v___x_657_ = l_Lean_Meta_isCoeDecl(v_env_655_, v_declName_656_);
if (v___x_657_ == 0)
{
lean_dec(v_declName_656_);
lean_dec_ref(v_e_640_);
v___y_648_ = v___y_641_;
goto v___jp_647_;
}
else
{
lean_object* v___x_658_; 
lean_inc(v_declName_656_);
lean_inc_ref(v_e_640_);
v___x_658_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_640_, v_declName_656_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; uint8_t v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = 0;
v___x_661_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_659_, v___x_660_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_714_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v_snd_663_ = lean_ctor_get(v_a_662_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_662_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_a_662_, 0);
lean_dec(v_unused_715_);
v___x_665_ = v_a_662_;
v_isShared_666_ = v_isSharedCheck_714_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_dec(v_a_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_714_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; 
lean_inc_ref(v_e_640_);
v___x_667_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_640_, v___x_660_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_705_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_705_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_705_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_705_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
if (lean_obj_tag(v_a_668_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_704_; 
v_val_672_ = lean_ctor_get(v_a_668_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_a_668_);
if (v_isSharedCheck_704_ == 0)
{
v___x_674_ = v_a_668_;
v_isShared_675_ = v_isSharedCheck_704_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v_a_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_704_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___y_677_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_689_ = lean_name_eq(v_declName_656_, v___x_688_);
lean_dec(v_declName_656_);
if (v___x_689_ == 0)
{
lean_dec_ref(v_e_640_);
v___y_677_ = v_snd_663_;
goto v___jp_676_;
}
else
{
lean_object* v_dummy_690_; lean_object* v_nargs_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_dummy_690_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_691_ = l_Lean_Expr_getAppNumArgs(v_e_640_);
lean_inc(v_nargs_691_);
v___x_692_ = lean_mk_array(v_nargs_691_, v_dummy_690_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_sub(v_nargs_691_, v___x_693_);
lean_dec(v_nargs_691_);
v___x_695_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_640_, v___x_692_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v___x_697_ = lean_array_get_size(v___x_695_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec_ref(v___x_695_);
v___y_677_ = v_snd_663_;
goto v___jp_676_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_array_fget(v___x_695_, v___x_696_);
lean_dec_ref(v___x_695_);
v___x_700_ = l_Lean_Expr_getAppFn(v___x_699_);
lean_dec(v___x_699_);
v___x_701_ = l_Lean_Expr_isConst(v___x_700_);
if (v___x_701_ == 0)
{
lean_dec_ref(v___x_700_);
v___y_677_ = v_snd_663_;
goto v___jp_676_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = l_Lean_Expr_constName_x21(v___x_700_);
lean_dec_ref(v___x_700_);
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_snd_663_);
v___y_677_ = v___x_703_;
goto v___jp_676_;
}
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Expr_headBeta(v_val_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_687_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___y_677_);
lean_ctor_set(v___x_665_, 0, v___x_680_);
v___x_682_ = v___x_665_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___y_677_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_682_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_670_);
lean_dec(v_a_668_);
lean_del_object(v___x_665_);
lean_dec(v_declName_656_);
lean_dec_ref(v_e_640_);
v___y_648_ = v_snd_663_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_665_);
lean_dec(v_snd_663_);
lean_dec(v_declName_656_);
lean_dec_ref(v_e_640_);
v_a_706_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_667_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_667_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_declName_656_);
lean_dec_ref(v_e_640_);
v_a_716_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_661_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_661_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_declName_656_);
lean_dec(v___y_641_);
lean_dec_ref(v_e_640_);
v_a_724_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_658_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_658_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
v___jp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___y_648_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_expandCoe___lam__1(v_e_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_741_);
v___x_749_ = lean_apply_8(v_k_740_, v_b_743_, v___y_741_, v___y_742_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, lean_box(0));
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v_b_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_750_, v___y_751_, v___y_752_, v_b_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_751_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_760_, uint8_t v_bi_761_, lean_object* v_type_762_, lean_object* v_k_763_, uint8_t v_kind_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; 
lean_inc(v___y_765_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_772_, 0, v_k_763_);
lean_closure_set(v___f_772_, 1, v___y_765_);
lean_closure_set(v___f_772_, 2, v___y_766_);
v___x_773_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_760_, v_bi_761_, v_type_762_, v___f_772_, v_kind_764_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_773_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_773_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_790_, lean_object* v_bi_791_, lean_object* v_type_792_, lean_object* v_k_793_, lean_object* v_kind_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v_bi_boxed_802_; uint8_t v_kind_boxed_803_; lean_object* v_res_804_; 
v_bi_boxed_802_ = lean_unbox(v_bi_791_);
v_kind_boxed_803_ = lean_unbox(v_kind_794_);
v_res_804_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_790_, v_bi_boxed_802_, v_type_792_, v_k_793_, v_kind_boxed_803_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_795_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_805_);
lean_ctor_set(v___x_812_, 1, v___y_806_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_822_, lean_object* v_type_823_, lean_object* v_val_824_, lean_object* v_k_825_, uint8_t v_nondep_826_, uint8_t v_kind_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___f_835_; lean_object* v___x_836_; 
lean_inc(v___y_828_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_835_, 0, v_k_825_);
lean_closure_set(v___f_835_, 1, v___y_828_);
lean_closure_set(v___f_835_, 2, v___y_829_);
v___x_836_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_822_, v_type_823_, v_val_824_, v___f_835_, v_nondep_826_, v_kind_827_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_836_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_836_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_853_, lean_object* v_type_854_, lean_object* v_val_855_, lean_object* v_k_856_, lean_object* v_nondep_857_, lean_object* v_kind_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v_nondep_boxed_866_; uint8_t v_kind_boxed_867_; lean_object* v_res_868_; 
v_nondep_boxed_866_ = lean_unbox(v_nondep_857_);
v_kind_boxed_867_ = lean_unbox(v_kind_858_);
v_res_868_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_853_, v_type_854_, v_val_855_, v_k_856_, v_nondep_boxed_866_, v_kind_boxed_867_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_859_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_869_, lean_object* v_b_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_dec(v_b_870_);
lean_dec_ref(v_a_869_);
return v_x_871_;
}
else
{
lean_object* v_key_872_; lean_object* v_value_873_; lean_object* v_tail_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v_key_872_ = lean_ctor_get(v_x_871_, 0);
v_value_873_ = lean_ctor_get(v_x_871_, 1);
v_tail_874_ = lean_ctor_get(v_x_871_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_886_ == 0)
{
v___x_876_ = v_x_871_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_tail_874_);
lean_inc(v_value_873_);
lean_inc(v_key_872_);
lean_dec(v_x_871_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_ExprStructEq_beq(v_key_872_, v_a_869_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_869_, v_b_870_, v_tail_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 2, v___x_879_);
v___x_881_ = v___x_876_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_key_872_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_value_873_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; 
lean_dec(v_value_873_);
lean_dec(v_key_872_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_b_870_);
lean_ctor_set(v___x_876_, 0, v_a_869_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_869_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_b_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_tail_874_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 0)
{
uint8_t v___x_889_; 
v___x_889_ = 0;
return v___x_889_;
}
else
{
lean_object* v_key_890_; lean_object* v_tail_891_; uint8_t v___x_892_; 
v_key_890_ = lean_ctor_get(v_x_888_, 0);
v_tail_891_ = lean_ctor_get(v_x_888_, 2);
v___x_892_ = l_Lean_ExprStructEq_beq(v_key_890_, v_a_887_);
if (v___x_892_ == 0)
{
v_x_888_ = v_tail_891_;
goto _start;
}
else
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_894_, v_x_895_);
lean_dec(v_x_895_);
lean_dec_ref(v_a_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
return v_x_898_;
}
else
{
lean_object* v_key_900_; lean_object* v_value_901_; lean_object* v_tail_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_925_; 
v_key_900_ = lean_ctor_get(v_x_899_, 0);
v_value_901_ = lean_ctor_get(v_x_899_, 1);
v_tail_902_ = lean_ctor_get(v_x_899_, 2);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_899_);
if (v_isSharedCheck_925_ == 0)
{
v___x_904_ = v_x_899_;
v_isShared_905_ = v_isSharedCheck_925_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_tail_902_);
lean_inc(v_value_901_);
lean_inc(v_key_900_);
lean_dec(v_x_899_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_925_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_fold_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_906_ = lean_array_get_size(v_x_898_);
v___x_907_ = l_Lean_ExprStructEq_hash(v_key_900_);
v___x_908_ = 32ULL;
v___x_909_ = lean_uint64_shift_right(v___x_907_, v___x_908_);
v_fold_910_ = lean_uint64_xor(v___x_907_, v___x_909_);
v___x_911_ = 16ULL;
v___x_912_ = lean_uint64_shift_right(v_fold_910_, v___x_911_);
v___x_913_ = lean_uint64_xor(v_fold_910_, v___x_912_);
v___x_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = lean_usize_of_nat(v___x_906_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_sub(v___x_915_, v___x_916_);
v___x_918_ = lean_usize_land(v___x_914_, v___x_917_);
v___x_919_ = lean_array_uget_borrowed(v_x_898_, v___x_918_);
lean_inc(v___x_919_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 2, v___x_919_);
v___x_921_ = v___x_904_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_key_900_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_value_901_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_919_);
v___x_921_ = v_reuseFailAlloc_924_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_array_uset(v_x_898_, v___x_918_, v___x_921_);
v_x_898_ = v___x_922_;
v_x_899_ = v_tail_902_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_926_, lean_object* v_source_927_, lean_object* v_target_928_){
_start:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_array_get_size(v_source_927_);
v___x_930_ = lean_nat_dec_lt(v_i_926_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_source_927_);
lean_dec(v_i_926_);
return v_target_928_;
}
else
{
lean_object* v_es_931_; lean_object* v___x_932_; lean_object* v_source_933_; lean_object* v_target_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_es_931_ = lean_array_fget(v_source_927_, v_i_926_);
v___x_932_ = lean_box(0);
v_source_933_ = lean_array_fset(v_source_927_, v_i_926_, v___x_932_);
v_target_934_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_928_, v_es_931_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_add(v_i_926_, v___x_935_);
lean_dec(v_i_926_);
v_i_926_ = v___x_936_;
v_source_927_ = v_source_933_;
v_target_928_ = v_target_934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_nbuckets_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_939_ = lean_array_get_size(v_data_938_);
v___x_940_ = lean_unsigned_to_nat(2u);
v_nbuckets_941_ = lean_nat_mul(v___x_939_, v___x_940_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_box(0);
v___x_944_ = lean_mk_array(v_nbuckets_941_, v___x_943_);
v___x_945_ = lean_array_propagate_mark(v_data_938_, v___x_944_);
v___x_946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_942_, v_data_938_, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_947_, lean_object* v_a_948_, lean_object* v_b_949_){
_start:
{
lean_object* v_size_950_; lean_object* v_buckets_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_994_; 
v_size_950_ = lean_ctor_get(v_m_947_, 0);
v_buckets_951_ = lean_ctor_get(v_m_947_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_m_947_);
if (v_isSharedCheck_994_ == 0)
{
v___x_953_ = v_m_947_;
v_isShared_954_ = v_isSharedCheck_994_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_buckets_951_);
lean_inc(v_size_950_);
lean_dec(v_m_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_994_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; uint64_t v___x_956_; uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v_fold_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v_bkt_968_; uint8_t v___x_969_; 
v___x_955_ = lean_array_get_size(v_buckets_951_);
v___x_956_ = l_Lean_ExprStructEq_hash(v_a_948_);
v___x_957_ = 32ULL;
v___x_958_ = lean_uint64_shift_right(v___x_956_, v___x_957_);
v_fold_959_ = lean_uint64_xor(v___x_956_, v___x_958_);
v___x_960_ = 16ULL;
v___x_961_ = lean_uint64_shift_right(v_fold_959_, v___x_960_);
v___x_962_ = lean_uint64_xor(v_fold_959_, v___x_961_);
v___x_963_ = lean_uint64_to_usize(v___x_962_);
v___x_964_ = lean_usize_of_nat(v___x_955_);
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_sub(v___x_964_, v___x_965_);
v___x_967_ = lean_usize_land(v___x_963_, v___x_966_);
v_bkt_968_ = lean_array_uget_borrowed(v_buckets_951_, v___x_967_);
v___x_969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_948_, v_bkt_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v_size_x27_971_; lean_object* v___x_972_; lean_object* v_buckets_x27_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v_size_x27_971_ = lean_nat_add(v_size_950_, v___x_970_);
lean_dec(v_size_950_);
lean_inc(v_bkt_968_);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v_a_948_);
lean_ctor_set(v___x_972_, 1, v_b_949_);
lean_ctor_set(v___x_972_, 2, v_bkt_968_);
v_buckets_x27_973_ = lean_array_uset(v_buckets_951_, v___x_967_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(4u);
v___x_975_ = lean_nat_mul(v_size_x27_971_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(3u);
v___x_977_ = lean_nat_div(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_array_get_size(v_buckets_x27_973_);
v___x_979_ = lean_nat_dec_le(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
if (v___x_979_ == 0)
{
lean_object* v_val_980_; lean_object* v___x_982_; 
v_val_980_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_973_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_val_980_);
lean_ctor_set(v___x_953_, 0, v_size_x27_971_);
v___x_982_ = v___x_953_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_size_x27_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_val_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_985_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_buckets_x27_973_);
lean_ctor_set(v___x_953_, 0, v_size_x27_971_);
v___x_985_ = v___x_953_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_size_x27_971_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_buckets_x27_973_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v___x_987_; lean_object* v_buckets_x27_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
lean_inc(v_bkt_968_);
v___x_987_ = lean_box(0);
v_buckets_x27_988_ = lean_array_uset(v_buckets_951_, v___x_967_, v___x_987_);
v___x_989_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_948_, v_b_949_, v_bkt_968_);
v___x_990_ = lean_array_uset(v_buckets_x27_988_, v___x_967_, v___x_989_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_990_);
v___x_992_ = v___x_953_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_size_950_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_995_, lean_object* v_e_996_, lean_object* v_fst_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = lean_st_ref_take(v_a_995_);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_999_, v_e_996_, v_fst_997_);
v___x_1001_ = lean_st_ref_put(v_a_995_, v___x_1000_);
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1003_, lean_object* v_e_1004_, lean_object* v_fst_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1003_, v_e_1004_, v_fst_1005_);
lean_dec(v_a_1003_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = l_Lean_maxRecDepthErrorMessage;
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1016_ = l_Lean_MessageData_ofFormat(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1018_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1019_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_ref_1020_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___y_1037_; lean_object* v_toCold_1054_; lean_object* v_currRecDepth_1055_; lean_object* v_ref_1056_; uint8_t v_diag_1057_; uint8_t v_suppressElabErrors_1058_; lean_object* v_maxRecDepth_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_toCold_1054_ = lean_ctor_get(v___y_1033_, 0);
v_currRecDepth_1055_ = lean_ctor_get(v___y_1033_, 1);
v_ref_1056_ = lean_ctor_get(v___y_1033_, 2);
v_diag_1057_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*3);
v_suppressElabErrors_1058_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*3 + 1);
v_maxRecDepth_1064_ = lean_ctor_get(v_toCold_1054_, 3);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_nat_dec_eq(v_maxRecDepth_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_nat_dec_eq(v_currRecDepth_1055_, v_maxRecDepth_1064_);
if (v___x_1067_ == 0)
{
goto v___jp_1059_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v___y_1030_);
lean_dec_ref(v_x_1028_);
lean_inc(v_ref_1056_);
v___x_1068_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1056_);
v___y_1037_ = v___x_1068_;
goto v___jp_1036_;
}
}
else
{
goto v___jp_1059_;
}
v___jp_1036_:
{
if (lean_obj_tag(v___y_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___y_1037_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1037_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___y_1037_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___y_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___y_1037_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___y_1037_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___y_1037_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___y_1037_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_currRecDepth_1055_, v___x_1060_);
lean_inc(v_ref_1056_);
lean_inc_ref(v_toCold_1054_);
v___x_1062_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1062_, 0, v_toCold_1054_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
lean_ctor_set(v___x_1062_, 2, v_ref_1056_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3, v_diag_1057_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*3 + 1, v_suppressElabErrors_1058_);
lean_inc(v___y_1034_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1029_);
v___x_1063_ = lean_apply_7(v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___x_1062_, v___y_1034_, lean_box(0));
v___y_1037_ = v___x_1063_;
goto v___jp_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1070_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_box(0);
return v___x_1080_;
}
else
{
lean_object* v_key_1081_; lean_object* v_value_1082_; lean_object* v_tail_1083_; uint8_t v___x_1084_; 
v_key_1081_ = lean_ctor_get(v_x_1079_, 0);
v_value_1082_ = lean_ctor_get(v_x_1079_, 1);
v_tail_1083_ = lean_ctor_get(v_x_1079_, 2);
v___x_1084_ = l_Lean_ExprStructEq_beq(v_key_1081_, v_a_1078_);
if (v___x_1084_ == 0)
{
v_x_1079_ = v_tail_1083_;
goto _start;
}
else
{
lean_object* v___x_1086_; 
lean_inc(v_value_1082_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_value_1082_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1087_, v_x_1088_);
lean_dec(v_x_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_buckets_1092_; lean_object* v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v_fold_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_buckets_1092_ = lean_ctor_get(v_m_1090_, 1);
v___x_1093_ = lean_array_get_size(v_buckets_1092_);
v___x_1094_ = l_Lean_ExprStructEq_hash(v_a_1091_);
v___x_1095_ = 32ULL;
v___x_1096_ = lean_uint64_shift_right(v___x_1094_, v___x_1095_);
v_fold_1097_ = lean_uint64_xor(v___x_1094_, v___x_1096_);
v___x_1098_ = 16ULL;
v___x_1099_ = lean_uint64_shift_right(v_fold_1097_, v___x_1098_);
v___x_1100_ = lean_uint64_xor(v_fold_1097_, v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = lean_usize_of_nat(v___x_1093_);
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_sub(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_usize_land(v___x_1101_, v___x_1104_);
v___x_1106_ = lean_array_uget_borrowed(v_buckets_1092_, v___x_1105_);
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1091_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1108_, v_a_1109_);
lean_dec_ref(v_a_1109_);
lean_dec_ref(v_m_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1111_, lean_object* v_x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_apply_1(v_x_1112_, lean_box(0));
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___y_1113_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1122_, v_x_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1134_, lean_object* v_pre_1135_, lean_object* v_post_1136_, uint8_t v_usedLetOnly_1137_, uint8_t v_skipConstInApp_1138_, uint8_t v_skipInstances_1139_, lean_object* v_body_1140_, lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_array_push(v_fvars_1134_, v_x_1141_);
v___x_1150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1135_, v_post_1136_, v_usedLetOnly_1137_, v_skipConstInApp_1138_, v_skipInstances_1139_, v___x_1149_, v_body_1140_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1151_, lean_object* v_pre_1152_, lean_object* v_post_1153_, lean_object* v_usedLetOnly_1154_, lean_object* v_skipConstInApp_1155_, lean_object* v_skipInstances_1156_, lean_object* v_body_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_usedLetOnly_boxed_1166_; uint8_t v_skipConstInApp_boxed_1167_; uint8_t v_skipInstances_boxed_1168_; lean_object* v_res_1169_; 
v_usedLetOnly_boxed_1166_ = lean_unbox(v_usedLetOnly_1154_);
v_skipConstInApp_boxed_1167_ = lean_unbox(v_skipConstInApp_1155_);
v_skipInstances_boxed_1168_ = lean_unbox(v_skipInstances_1156_);
v_res_1169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1151_, v_pre_1152_, v_post_1153_, v_usedLetOnly_boxed_1166_, v_skipConstInApp_boxed_1167_, v_skipInstances_boxed_1168_, v_body_1157_, v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1159_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1170_, lean_object* v_post_1171_, uint8_t v_usedLetOnly_1172_, uint8_t v_skipConstInApp_1173_, uint8_t v_skipInstances_1174_, lean_object* v_e_1175_, lean_object* v_a_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
lean_inc_ref(v_post_1171_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc_ref(v_e_1175_);
v___x_1183_ = lean_apply_7(v_post_1171_, v_e_1175_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, lean_box(0));
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1215_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1215_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1215_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1214_; 
v_fst_1188_ = lean_ctor_get(v_a_1184_, 0);
v_snd_1189_ = lean_ctor_get(v_a_1184_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1184_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1191_ = v_a_1184_;
v_isShared_1192_ = v_isSharedCheck_1214_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_snd_1189_);
lean_inc(v_fst_1188_);
lean_dec(v_a_1184_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1214_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___y_1194_; 
switch(lean_obj_tag(v_fst_1188_))
{
case 0:
{
lean_object* v_e_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
lean_del_object(v___x_1191_);
lean_del_object(v___x_1186_);
lean_dec_ref(v_e_1175_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_e_1201_ = lean_ctor_get(v_fst_1188_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_fst_1188_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1203_ = v_fst_1188_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_e_1201_);
lean_dec(v_fst_1188_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_e_1201_);
lean_ctor_set(v___x_1205_, 1, v_snd_1189_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
case 1:
{
lean_object* v_e_1210_; lean_object* v___x_1211_; 
lean_del_object(v___x_1191_);
lean_del_object(v___x_1186_);
lean_dec_ref(v_e_1175_);
v_e_1210_ = lean_ctor_get(v_fst_1188_, 0);
lean_inc_ref(v_e_1210_);
lean_dec_ref_known(v_fst_1188_, 1);
v___x_1211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1174_, v_e_1210_, v_a_1176_, v_snd_1189_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1211_;
}
default: 
{
lean_object* v_e_x3f_1212_; 
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_e_x3f_1212_ = lean_ctor_get(v_fst_1188_, 0);
lean_inc(v_e_x3f_1212_);
lean_dec_ref_known(v_fst_1188_, 1);
if (lean_obj_tag(v_e_x3f_1212_) == 0)
{
v___y_1194_ = v_e_1175_;
goto v___jp_1193_;
}
else
{
lean_object* v_val_1213_; 
lean_dec_ref(v_e_1175_);
v_val_1213_ = lean_ctor_get(v_e_x3f_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v_e_x3f_1212_, 1);
v___y_1194_ = v_val_1213_;
goto v___jp_1193_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___y_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___y_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_snd_1189_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1196_);
v___x_1198_ = v___x_1186_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_e_1175_);
lean_dec_ref(v_post_1171_);
lean_dec_ref(v_pre_1170_);
v_a_1216_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1183_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1183_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1224_, lean_object* v_post_1225_, uint8_t v_usedLetOnly_1226_, uint8_t v_skipConstInApp_1227_, uint8_t v_skipInstances_1228_, lean_object* v_fvars_1229_, lean_object* v_e_1230_, lean_object* v_a_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
if (lean_obj_tag(v_e_1230_) == 6)
{
lean_object* v_binderName_1238_; lean_object* v_binderType_1239_; lean_object* v_body_1240_; uint8_t v_binderInfo_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_binderName_1238_ = lean_ctor_get(v_e_1230_, 0);
lean_inc(v_binderName_1238_);
v_binderType_1239_ = lean_ctor_get(v_e_1230_, 1);
lean_inc_ref(v_binderType_1239_);
v_body_1240_ = lean_ctor_get(v_e_1230_, 2);
lean_inc_ref(v_body_1240_);
v_binderInfo_1241_ = lean_ctor_get_uint8(v_e_1230_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1230_, 3);
v___x_1242_ = lean_expr_instantiate_rev(v_binderType_1239_, v_fvars_1229_);
lean_dec_ref(v_binderType_1239_);
lean_inc_ref(v_post_1225_);
lean_inc_ref(v_pre_1224_);
v___x_1243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1224_, v_post_1225_, v_usedLetOnly_1226_, v_skipConstInApp_1227_, v_skipInstances_1228_, v___x_1242_, v_a_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_fst_1245_; lean_object* v_snd_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___f_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v_fst_1245_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_fst_1245_);
v_snd_1246_ = lean_ctor_get(v_a_1244_, 1);
lean_inc(v_snd_1246_);
lean_dec(v_a_1244_);
v___x_1247_ = lean_box(v_usedLetOnly_1226_);
v___x_1248_ = lean_box(v_skipConstInApp_1227_);
v___x_1249_ = lean_box(v_skipInstances_1228_);
v___f_1250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1250_, 0, v_fvars_1229_);
lean_closure_set(v___f_1250_, 1, v_pre_1224_);
lean_closure_set(v___f_1250_, 2, v_post_1225_);
lean_closure_set(v___f_1250_, 3, v___x_1247_);
lean_closure_set(v___f_1250_, 4, v___x_1248_);
lean_closure_set(v___f_1250_, 5, v___x_1249_);
lean_closure_set(v___f_1250_, 6, v_body_1240_);
v___x_1251_ = 0;
v___x_1252_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1238_, v_binderInfo_1241_, v_fst_1245_, v___f_1250_, v___x_1251_, v_a_1231_, v_snd_1246_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1252_;
}
else
{
lean_dec_ref(v_body_1240_);
lean_dec(v_binderName_1238_);
lean_dec_ref(v_fvars_1229_);
lean_dec_ref(v_post_1225_);
lean_dec_ref(v_pre_1224_);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_expr_instantiate_rev(v_e_1230_, v_fvars_1229_);
lean_dec_ref(v_e_1230_);
lean_inc_ref(v_post_1225_);
lean_inc_ref(v_pre_1224_);
v___x_1254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1224_, v_post_1225_, v_usedLetOnly_1226_, v_skipConstInApp_1227_, v_skipInstances_1228_, v___x_1253_, v_a_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; uint8_t v___x_1258_; uint8_t v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_fst_1256_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1257_);
lean_dec(v_a_1255_);
v___x_1258_ = 0;
v___x_1259_ = 1;
v___x_1260_ = 1;
v___x_1261_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1229_, v_fst_1256_, v___x_1258_, v_usedLetOnly_1226_, v___x_1258_, v___x_1259_, v___x_1260_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec_ref(v_fvars_1229_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1224_, v_post_1225_, v_usedLetOnly_1226_, v_skipConstInApp_1227_, v_skipInstances_1228_, v_a_1262_, v_a_1231_, v_snd_1257_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1263_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_snd_1257_);
lean_dec_ref(v_post_1225_);
lean_dec_ref(v_pre_1224_);
v_a_1264_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1261_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1229_);
lean_dec_ref(v_post_1225_);
lean_dec_ref(v_pre_1224_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1272_, lean_object* v_pre_1273_, lean_object* v_post_1274_, uint8_t v_usedLetOnly_1275_, uint8_t v_skipConstInApp_1276_, uint8_t v_skipInstances_1277_, lean_object* v_body_1278_, lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_array_push(v_fvars_1272_, v_x_1279_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1273_, v_post_1274_, v_usedLetOnly_1275_, v_skipConstInApp_1276_, v_skipInstances_1277_, v___x_1287_, v_body_1278_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1289_, lean_object* v_pre_1290_, lean_object* v_post_1291_, lean_object* v_usedLetOnly_1292_, lean_object* v_skipConstInApp_1293_, lean_object* v_skipInstances_1294_, lean_object* v_body_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_usedLetOnly_boxed_1304_; uint8_t v_skipConstInApp_boxed_1305_; uint8_t v_skipInstances_boxed_1306_; lean_object* v_res_1307_; 
v_usedLetOnly_boxed_1304_ = lean_unbox(v_usedLetOnly_1292_);
v_skipConstInApp_boxed_1305_ = lean_unbox(v_skipConstInApp_1293_);
v_skipInstances_boxed_1306_ = lean_unbox(v_skipInstances_1294_);
v_res_1307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1289_, v_pre_1290_, v_post_1291_, v_usedLetOnly_boxed_1304_, v_skipConstInApp_boxed_1305_, v_skipInstances_boxed_1306_, v_body_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1297_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1308_, lean_object* v_post_1309_, uint8_t v_usedLetOnly_1310_, uint8_t v_skipConstInApp_1311_, uint8_t v_skipInstances_1312_, lean_object* v_fvars_1313_, lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
if (lean_obj_tag(v_e_1314_) == 8)
{
lean_object* v_declName_1322_; lean_object* v_type_1323_; lean_object* v_value_1324_; lean_object* v_body_1325_; uint8_t v_nondep_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_declName_1322_ = lean_ctor_get(v_e_1314_, 0);
lean_inc(v_declName_1322_);
v_type_1323_ = lean_ctor_get(v_e_1314_, 1);
lean_inc_ref(v_type_1323_);
v_value_1324_ = lean_ctor_get(v_e_1314_, 2);
lean_inc_ref(v_value_1324_);
v_body_1325_ = lean_ctor_get(v_e_1314_, 3);
lean_inc_ref(v_body_1325_);
v_nondep_1326_ = lean_ctor_get_uint8(v_e_1314_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1314_, 4);
v___x_1327_ = lean_expr_instantiate_rev(v_type_1323_, v_fvars_1313_);
lean_dec_ref(v_type_1323_);
lean_inc_ref(v_post_1309_);
lean_inc_ref(v_pre_1308_);
v___x_1328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1308_, v_post_1309_, v_usedLetOnly_1310_, v_skipConstInApp_1311_, v_skipInstances_1312_, v___x_1327_, v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_fst_1330_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_a_1329_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1329_);
v___x_1332_ = lean_expr_instantiate_rev(v_value_1324_, v_fvars_1313_);
lean_dec_ref(v_value_1324_);
lean_inc_ref(v_post_1309_);
lean_inc_ref(v_pre_1308_);
v___x_1333_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1308_, v_post_1309_, v_usedLetOnly_1310_, v_skipConstInApp_1311_, v_skipInstances_1312_, v___x_1332_, v_a_1315_, v_snd_1331_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___f_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_fst_1335_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_fst_1335_);
v_snd_1336_ = lean_ctor_get(v_a_1334_, 1);
lean_inc(v_snd_1336_);
lean_dec(v_a_1334_);
v___x_1337_ = lean_box(v_usedLetOnly_1310_);
v___x_1338_ = lean_box(v_skipConstInApp_1311_);
v___x_1339_ = lean_box(v_skipInstances_1312_);
v___f_1340_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1340_, 0, v_fvars_1313_);
lean_closure_set(v___f_1340_, 1, v_pre_1308_);
lean_closure_set(v___f_1340_, 2, v_post_1309_);
lean_closure_set(v___f_1340_, 3, v___x_1337_);
lean_closure_set(v___f_1340_, 4, v___x_1338_);
lean_closure_set(v___f_1340_, 5, v___x_1339_);
lean_closure_set(v___f_1340_, 6, v_body_1325_);
v___x_1341_ = 0;
v___x_1342_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1322_, v_fst_1330_, v_fst_1335_, v___f_1340_, v_nondep_1326_, v___x_1341_, v_a_1315_, v_snd_1336_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1342_;
}
else
{
lean_dec(v_fst_1330_);
lean_dec_ref(v_body_1325_);
lean_dec(v_declName_1322_);
lean_dec_ref(v_fvars_1313_);
lean_dec_ref(v_post_1309_);
lean_dec_ref(v_pre_1308_);
return v___x_1333_;
}
}
else
{
lean_dec_ref(v_body_1325_);
lean_dec_ref(v_value_1324_);
lean_dec(v_declName_1322_);
lean_dec_ref(v_fvars_1313_);
lean_dec_ref(v_post_1309_);
lean_dec_ref(v_pre_1308_);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_expr_instantiate_rev(v_e_1314_, v_fvars_1313_);
lean_dec_ref(v_e_1314_);
lean_inc_ref(v_post_1309_);
lean_inc_ref(v_pre_1308_);
v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1308_, v_post_1309_, v_usedLetOnly_1310_, v_skipConstInApp_1311_, v_skipInstances_1312_, v___x_1343_, v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v_fst_1346_ = lean_ctor_get(v_a_1345_, 0);
lean_inc(v_fst_1346_);
v_snd_1347_ = lean_ctor_get(v_a_1345_, 1);
lean_inc(v_snd_1347_);
lean_dec(v_a_1345_);
v___x_1348_ = 0;
v___x_1349_ = 1;
v___x_1350_ = l_Lean_Meta_mkLetFVars(v_fvars_1313_, v_fst_1346_, v_usedLetOnly_1310_, v___x_1348_, v___x_1349_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v_fvars_1313_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1308_, v_post_1309_, v_usedLetOnly_1310_, v_skipConstInApp_1311_, v_skipInstances_1312_, v_a_1351_, v_a_1315_, v_snd_1347_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1352_;
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_snd_1347_);
lean_dec_ref(v_post_1309_);
lean_dec_ref(v_pre_1308_);
v_a_1353_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1350_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1350_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1313_);
lean_dec_ref(v_post_1309_);
lean_dec_ref(v_pre_1308_);
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1361_, lean_object* v_post_1362_, uint8_t v_usedLetOnly_1363_, uint8_t v_skipConstInApp_1364_, uint8_t v_skipInstances_1365_, size_t v_sz_1366_, size_t v_i_1367_, lean_object* v_bs_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1367_, v_sz_1366_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v_post_1362_);
lean_dec_ref(v_pre_1361_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_bs_1368_);
lean_ctor_set(v___x_1377_, 1, v___y_1370_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
else
{
lean_object* v_v_1379_; lean_object* v___x_1380_; 
v_v_1379_ = lean_array_uget_borrowed(v_bs_1368_, v_i_1367_);
lean_inc(v_v_1379_);
lean_inc_ref(v_post_1362_);
lean_inc_ref(v_pre_1361_);
v___x_1380_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1361_, v_post_1362_, v_usedLetOnly_1363_, v_skipConstInApp_1364_, v_skipInstances_1365_, v_v_1379_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1384_; lean_object* v_bs_x27_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_fst_1382_ = lean_ctor_get(v_a_1381_, 0);
lean_inc(v_fst_1382_);
v_snd_1383_ = lean_ctor_get(v_a_1381_, 1);
lean_inc(v_snd_1383_);
lean_dec(v_a_1381_);
v___x_1384_ = lean_unsigned_to_nat(0u);
v_bs_x27_1385_ = lean_array_uset(v_bs_1368_, v_i_1367_, v___x_1384_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1367_, v___x_1386_);
v___x_1388_ = lean_array_uset(v_bs_x27_1385_, v_i_1367_, v_fst_1382_);
v_i_1367_ = v___x_1387_;
v_bs_1368_ = v___x_1388_;
v___y_1370_ = v_snd_1383_;
goto _start;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_bs_1368_);
lean_dec_ref(v_post_1362_);
lean_dec_ref(v_pre_1361_);
v_a_1390_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1380_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1380_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1398_, lean_object* v_post_1399_, uint8_t v_usedLetOnly_1400_, uint8_t v_skipConstInApp_1401_, uint8_t v_skipInstances_1402_, lean_object* v___x_1403_, lean_object* v___y_1404_, lean_object* v_b_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1398_, v_post_1399_, v_usedLetOnly_1400_, v_skipConstInApp_1401_, v_skipInstances_1402_, v___x_1403_, v___y_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1432_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1431_; 
v_fst_1418_ = lean_ctor_get(v_a_1414_, 0);
v_snd_1419_ = lean_ctor_get(v_a_1414_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_a_1414_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1421_ = v_a_1414_;
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_inc(v_fst_1418_);
lean_dec(v_a_1414_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_array_fset(v_b_1405_, v_a_1406_, v_fst_1418_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1419_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1426_);
v___x_1428_ = v___x_1416_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_b_1405_);
v_a_1433_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1413_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1413_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1441_, lean_object* v_post_1442_, lean_object* v_usedLetOnly_1443_, lean_object* v_skipConstInApp_1444_, lean_object* v_skipInstances_1445_, lean_object* v___x_1446_, lean_object* v___y_1447_, lean_object* v_b_1448_, lean_object* v_a_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v_usedLetOnly_boxed_1456_; uint8_t v_skipConstInApp_boxed_1457_; uint8_t v_skipInstances_boxed_1458_; lean_object* v_res_1459_; 
v_usedLetOnly_boxed_1456_ = lean_unbox(v_usedLetOnly_1443_);
v_skipConstInApp_boxed_1457_ = lean_unbox(v_skipConstInApp_1444_);
v_skipInstances_boxed_1458_ = lean_unbox(v_skipInstances_1445_);
v_res_1459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1441_, v_post_1442_, v_usedLetOnly_boxed_1456_, v_skipConstInApp_boxed_1457_, v_skipInstances_boxed_1458_, v___x_1446_, v___y_1447_, v_b_1448_, v_a_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v_a_1449_);
lean_dec(v___y_1447_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1460_, lean_object* v___x_1461_, lean_object* v_pre_1462_, lean_object* v_post_1463_, uint8_t v_usedLetOnly_1464_, uint8_t v_skipConstInApp_1465_, uint8_t v_skipInstances_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___y_1477_; uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_lt(v_a_1467_, v_upperBound_1460_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_a_1467_);
lean_dec_ref(v_post_1463_);
lean_dec_ref(v_pre_1462_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_b_1468_);
lean_ctor_set(v___x_1512_, 1, v___y_1470_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_array_fget_borrowed(v_b_1468_, v_a_1467_);
v___x_1515_ = lean_array_get_size(v___x_1461_);
v___x_1516_ = lean_nat_dec_lt(v_a_1467_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; 
lean_inc(v___x_1514_);
v___x_1517_ = lean_box(v_usedLetOnly_1464_);
v___x_1518_ = lean_box(v_skipConstInApp_1465_);
v___x_1519_ = lean_box(v_skipInstances_1466_);
lean_inc(v_a_1467_);
lean_inc(v___y_1469_);
lean_inc_ref(v_post_1463_);
lean_inc_ref(v_pre_1462_);
v___f_1520_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1520_, 0, v_pre_1462_);
lean_closure_set(v___f_1520_, 1, v_post_1463_);
lean_closure_set(v___f_1520_, 2, v___x_1517_);
lean_closure_set(v___f_1520_, 3, v___x_1518_);
lean_closure_set(v___f_1520_, 4, v___x_1519_);
lean_closure_set(v___f_1520_, 5, v___x_1514_);
lean_closure_set(v___f_1520_, 6, v___y_1469_);
lean_closure_set(v___f_1520_, 7, v_b_1468_);
lean_closure_set(v___f_1520_, 8, v_a_1467_);
v___y_1477_ = v___f_1520_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1521_; uint8_t v_isInstance_1522_; 
v___x_1521_ = lean_array_fget_borrowed(v___x_1461_, v_a_1467_);
v_isInstance_1522_ = lean_ctor_get_uint8(v___x_1521_, sizeof(void*)*1 + 4);
if (v_isInstance_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___f_1526_; 
lean_inc(v___x_1514_);
v___x_1523_ = lean_box(v_usedLetOnly_1464_);
v___x_1524_ = lean_box(v_skipConstInApp_1465_);
v___x_1525_ = lean_box(v_skipInstances_1466_);
lean_inc(v_a_1467_);
lean_inc(v___y_1469_);
lean_inc_ref(v_post_1463_);
lean_inc_ref(v_pre_1462_);
v___f_1526_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1526_, 0, v_pre_1462_);
lean_closure_set(v___f_1526_, 1, v_post_1463_);
lean_closure_set(v___f_1526_, 2, v___x_1523_);
lean_closure_set(v___f_1526_, 3, v___x_1524_);
lean_closure_set(v___f_1526_, 4, v___x_1525_);
lean_closure_set(v___f_1526_, 5, v___x_1514_);
lean_closure_set(v___f_1526_, 6, v___y_1469_);
lean_closure_set(v___f_1526_, 7, v_b_1468_);
lean_closure_set(v___f_1526_, 8, v_a_1467_);
v___y_1477_ = v___f_1526_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1527_; lean_object* v___f_1528_; 
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_b_1468_);
v___f_1528_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1528_, 0, v___x_1527_);
v___y_1477_ = v___f_1528_;
goto v___jp_1476_;
}
}
}
v___jp_1476_:
{
lean_object* v___x_1478_; 
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
v___x_1478_ = lean_apply_6(v___y_1477_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, lean_box(0));
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1502_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1502_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1502_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_fst_1483_; 
v_fst_1483_ = lean_ctor_get(v_a_1479_, 0);
lean_inc(v_fst_1483_);
if (lean_obj_tag(v_fst_1483_) == 0)
{
lean_object* v_snd_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1467_);
lean_dec_ref(v_post_1463_);
lean_dec_ref(v_pre_1462_);
v_snd_1484_ = lean_ctor_get(v_a_1479_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_a_1479_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_a_1479_, 0);
lean_dec(v_unused_1496_);
v___x_1486_ = v_a_1479_;
v_isShared_1487_ = v_isSharedCheck_1495_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1484_);
lean_dec(v_a_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1495_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_a_1488_; lean_object* v___x_1490_; 
v_a_1488_ = lean_ctor_get(v_fst_1483_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v_fst_1483_, 1);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v_a_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_snd_1484_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1490_);
v___x_1492_ = v___x_1481_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_snd_1497_; lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_del_object(v___x_1481_);
v_snd_1497_ = lean_ctor_get(v_a_1479_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_a_1479_);
v_a_1498_ = lean_ctor_get(v_fst_1483_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v_fst_1483_, 1);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_a_1467_, v___x_1499_);
lean_dec(v_a_1467_);
v_a_1467_ = v___x_1500_;
v_b_1468_ = v_a_1498_;
v___y_1470_ = v_snd_1497_;
goto _start;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1467_);
lean_dec_ref(v_post_1463_);
lean_dec_ref(v_pre_1462_);
v_a_1503_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1478_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1478_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1529_, lean_object* v_pre_1530_, lean_object* v_post_1531_, uint8_t v_usedLetOnly_1532_, uint8_t v_skipConstInApp_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_f_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; 
if (lean_obj_tag(v_x_1534_) == 5)
{
lean_object* v_fn_1600_; lean_object* v_arg_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_fn_1600_ = lean_ctor_get(v_x_1534_, 0);
lean_inc_ref(v_fn_1600_);
v_arg_1601_ = lean_ctor_get(v_x_1534_, 1);
lean_inc_ref(v_arg_1601_);
lean_dec_ref_known(v_x_1534_, 2);
v___x_1602_ = lean_array_set(v_x_1535_, v_x_1536_, v_arg_1601_);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_sub(v_x_1536_, v___x_1603_);
lean_dec(v_x_1536_);
v_x_1534_ = v_fn_1600_;
v_x_1535_ = v___x_1602_;
v_x_1536_ = v___x_1604_;
goto _start;
}
else
{
lean_dec(v_x_1536_);
if (v_skipConstInApp_1533_ == 0)
{
goto v___jp_1595_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Expr_isConst(v_x_1534_);
if (v___x_1606_ == 0)
{
goto v___jp_1595_;
}
else
{
v_f_1545_ = v_x_1534_;
v___y_1546_ = v___y_1537_;
v___y_1547_ = v___y_1538_;
v___y_1548_ = v___y_1539_;
v___y_1549_ = v___y_1540_;
v___y_1550_ = v___y_1541_;
v___y_1551_ = v___y_1542_;
goto v___jp_1544_;
}
}
}
v___jp_1544_:
{
if (v_skipInstances_1529_ == 0)
{
size_t v_sz_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v_sz_1552_ = lean_array_size(v_x_1535_);
v___x_1553_ = ((size_t)0ULL);
lean_inc_ref(v_post_1531_);
lean_inc_ref(v_pre_1530_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1530_, v_post_1531_, v_usedLetOnly_1532_, v_skipConstInApp_1533_, v_skipInstances_1529_, v_sz_1552_, v___x_1553_, v_x_1535_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_fst_1556_; lean_object* v_snd_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_fst_1556_ = lean_ctor_get(v_a_1555_, 0);
lean_inc(v_fst_1556_);
v_snd_1557_ = lean_ctor_get(v_a_1555_, 1);
lean_inc(v_snd_1557_);
lean_dec(v_a_1555_);
v___x_1558_ = l_Lean_mkAppN(v_f_1545_, v_fst_1556_);
lean_dec(v_fst_1556_);
v___x_1559_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1530_, v_post_1531_, v_usedLetOnly_1532_, v_skipConstInApp_1533_, v_skipInstances_1529_, v___x_1558_, v___y_1546_, v_snd_1557_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1559_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_f_1545_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v_a_1560_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1554_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1554_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_array_get_size(v_x_1535_);
lean_inc_ref(v_f_1545_);
v___x_1569_ = l_Lean_Meta_getFunInfoNArgs(v_f_1545_, v___x_1568_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_paramInfo_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v_paramInfo_1571_ = lean_ctor_get(v_a_1570_, 0);
lean_inc_ref(v_paramInfo_1571_);
lean_dec(v_a_1570_);
v___x_1572_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1531_);
lean_inc_ref(v_pre_1530_);
v___x_1573_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1568_, v_paramInfo_1571_, v_pre_1530_, v_post_1531_, v_usedLetOnly_1532_, v_skipConstInApp_1533_, v_skipInstances_1529_, v___x_1572_, v_x_1535_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_paramInfo_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_fst_1575_; lean_object* v_snd_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_fst_1575_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_fst_1575_);
v_snd_1576_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1576_);
lean_dec(v_a_1574_);
v___x_1577_ = l_Lean_mkAppN(v_f_1545_, v_fst_1575_);
lean_dec(v_fst_1575_);
v___x_1578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1530_, v_post_1531_, v_usedLetOnly_1532_, v_skipConstInApp_1533_, v_skipInstances_1529_, v___x_1577_, v___y_1546_, v_snd_1576_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_f_1545_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v_a_1579_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1573_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1573_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v___y_1547_);
lean_dec_ref(v_f_1545_);
lean_dec_ref(v_x_1535_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
v_a_1587_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1569_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1569_);
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
}
v___jp_1595_:
{
lean_object* v___x_1596_; 
lean_inc_ref(v_post_1531_);
lean_inc_ref(v_pre_1530_);
v___x_1596_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1530_, v_post_1531_, v_usedLetOnly_1532_, v_skipConstInApp_1533_, v_skipInstances_1529_, v_x_1534_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v_fst_1598_ = lean_ctor_get(v_a_1597_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v_a_1597_, 1);
lean_inc(v_snd_1599_);
lean_dec(v_a_1597_);
v_f_1545_ = v_fst_1598_;
v___y_1546_ = v___y_1537_;
v___y_1547_ = v_snd_1599_;
v___y_1548_ = v___y_1539_;
v___y_1549_ = v___y_1540_;
v___y_1550_ = v___y_1541_;
v___y_1551_ = v___y_1542_;
goto v___jp_1544_;
}
else
{
lean_dec_ref(v_x_1535_);
lean_dec_ref(v_post_1531_);
lean_dec_ref(v_pre_1530_);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1607_, lean_object* v_pre_1608_, lean_object* v_e_1609_, lean_object* v_post_1610_, uint8_t v_usedLetOnly_1611_, uint8_t v_skipConstInApp_1612_, uint8_t v_skipInstances_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Core_checkSystem(v___x_1607_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1621_, 1);
lean_inc_ref(v_pre_1608_);
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc_ref(v_e_1609_);
v___x_1622_ = lean_apply_7(v_pre_1608_, v_e_1609_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, lean_box(0));
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1684_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1684_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1684_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1683_; 
v_fst_1627_ = lean_ctor_get(v_a_1623_, 0);
v_snd_1628_ = lean_ctor_get(v_a_1623_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_a_1623_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1630_ = v_a_1623_;
v_isShared_1631_ = v_isSharedCheck_1683_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snd_1628_);
lean_inc(v_fst_1627_);
lean_dec(v_a_1623_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1683_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___y_1633_; 
switch(lean_obj_tag(v_fst_1627_))
{
case 0:
{
lean_object* v_e_1672_; lean_object* v___x_1674_; 
lean_dec_ref(v_post_1610_);
lean_dec_ref(v_e_1609_);
lean_dec_ref(v_pre_1608_);
v_e_1672_ = lean_ctor_get(v_fst_1627_, 0);
lean_inc_ref(v_e_1672_);
lean_dec_ref_known(v_fst_1627_, 1);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_e_1672_);
v___x_1674_ = v___x_1630_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_e_1672_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_snd_1628_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1674_);
v___x_1676_ = v___x_1625_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
case 1:
{
lean_object* v_e_1679_; lean_object* v___x_1680_; 
lean_del_object(v___x_1630_);
lean_del_object(v___x_1625_);
lean_dec_ref(v_e_1609_);
v_e_1679_ = lean_ctor_get(v_fst_1627_, 0);
lean_inc_ref(v_e_1679_);
lean_dec_ref_known(v_fst_1627_, 1);
v___x_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v_e_1679_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1680_;
}
default: 
{
lean_object* v_e_x3f_1681_; 
lean_del_object(v___x_1630_);
lean_del_object(v___x_1625_);
v_e_x3f_1681_ = lean_ctor_get(v_fst_1627_, 0);
lean_inc(v_e_x3f_1681_);
lean_dec_ref_known(v_fst_1627_, 1);
if (lean_obj_tag(v_e_x3f_1681_) == 0)
{
v___y_1633_ = v_e_1609_;
goto v___jp_1632_;
}
else
{
lean_object* v_val_1682_; 
lean_dec_ref(v_e_1609_);
v_val_1682_ = lean_ctor_get(v_e_x3f_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v_e_x3f_1681_, 1);
v___y_1633_ = v_val_1682_;
goto v___jp_1632_;
}
}
}
v___jp_1632_:
{
switch(lean_obj_tag(v___y_1633_))
{
case 7:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___x_1634_, v___y_1633_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1635_;
}
case 6:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1637_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___x_1636_, v___y_1633_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1637_;
}
case 8:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1639_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___x_1638_, v___y_1633_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1639_;
}
case 5:
{
lean_object* v_dummy_1640_; lean_object* v_nargs_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_dummy_1640_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1641_ = l_Lean_Expr_getAppNumArgs(v___y_1633_);
lean_inc(v_nargs_1641_);
v___x_1642_ = lean_mk_array(v_nargs_1641_, v_dummy_1640_);
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_sub(v_nargs_1641_, v___x_1643_);
lean_dec(v_nargs_1641_);
v___x_1645_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1613_, v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v___y_1633_, v___x_1642_, v___x_1644_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1645_;
}
case 10:
{
lean_object* v_data_1646_; lean_object* v_expr_1647_; lean_object* v___x_1648_; 
v_data_1646_ = lean_ctor_get(v___y_1633_, 0);
v_expr_1647_ = lean_ctor_get(v___y_1633_, 1);
lean_inc_ref(v_expr_1647_);
lean_inc_ref(v_post_1610_);
lean_inc_ref(v_pre_1608_);
v___x_1648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v_expr_1647_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v_fst_1650_; lean_object* v_snd_1651_; size_t v___x_1652_; size_t v___x_1653_; uint8_t v___x_1654_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v_fst_1650_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_fst_1650_);
v_snd_1651_ = lean_ctor_get(v_a_1649_, 1);
lean_inc(v_snd_1651_);
lean_dec(v_a_1649_);
v___x_1652_ = lean_ptr_addr(v_expr_1647_);
v___x_1653_ = lean_ptr_addr(v_fst_1650_);
v___x_1654_ = lean_usize_dec_eq(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_inc(v_data_1646_);
lean_dec_ref_known(v___y_1633_, 2);
v___x_1655_ = l_Lean_Expr_mdata___override(v_data_1646_, v_fst_1650_);
v___x_1656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___x_1655_, v___y_1614_, v_snd_1651_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
lean_dec(v_fst_1650_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___y_1633_, v___y_1614_, v_snd_1651_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1657_;
}
}
else
{
lean_dec_ref_known(v___y_1633_, 2);
lean_dec_ref(v_post_1610_);
lean_dec_ref(v_pre_1608_);
return v___x_1648_;
}
}
case 11:
{
lean_object* v_typeName_1658_; lean_object* v_idx_1659_; lean_object* v_struct_1660_; lean_object* v___x_1661_; 
v_typeName_1658_ = lean_ctor_get(v___y_1633_, 0);
v_idx_1659_ = lean_ctor_get(v___y_1633_, 1);
v_struct_1660_ = lean_ctor_get(v___y_1633_, 2);
lean_inc_ref(v_struct_1660_);
lean_inc_ref(v_post_1610_);
lean_inc_ref(v_pre_1608_);
v___x_1661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v_struct_1660_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v_fst_1663_; lean_object* v_snd_1664_; size_t v___x_1665_; size_t v___x_1666_; uint8_t v___x_1667_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v_fst_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_fst_1663_);
v_snd_1664_ = lean_ctor_get(v_a_1662_, 1);
lean_inc(v_snd_1664_);
lean_dec(v_a_1662_);
v___x_1665_ = lean_ptr_addr(v_struct_1660_);
v___x_1666_ = lean_ptr_addr(v_fst_1663_);
v___x_1667_ = lean_usize_dec_eq(v___x_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_inc(v_idx_1659_);
lean_inc(v_typeName_1658_);
lean_dec_ref_known(v___y_1633_, 3);
v___x_1668_ = l_Lean_Expr_proj___override(v_typeName_1658_, v_idx_1659_, v_fst_1663_);
v___x_1669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___x_1668_, v___y_1614_, v_snd_1664_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; 
lean_dec(v_fst_1663_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___y_1633_, v___y_1614_, v_snd_1664_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1670_;
}
}
else
{
lean_dec_ref_known(v___y_1633_, 3);
lean_dec_ref(v_post_1610_);
lean_dec_ref(v_pre_1608_);
return v___x_1661_;
}
}
default: 
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1608_, v_post_1610_, v_usedLetOnly_1611_, v_skipConstInApp_1612_, v_skipInstances_1613_, v___y_1633_, v___y_1614_, v_snd_1628_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1671_;
}
}
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_post_1610_);
lean_dec_ref(v_e_1609_);
lean_dec_ref(v_pre_1608_);
v_a_1685_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1622_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1622_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v___y_1615_);
lean_dec_ref(v_post_1610_);
lean_dec_ref(v_e_1609_);
lean_dec_ref(v_pre_1608_);
v_a_1693_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1621_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1621_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1701_, lean_object* v_pre_1702_, lean_object* v_e_1703_, lean_object* v_post_1704_, lean_object* v_usedLetOnly_1705_, lean_object* v_skipConstInApp_1706_, lean_object* v_skipInstances_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_usedLetOnly_boxed_1715_; uint8_t v_skipConstInApp_boxed_1716_; uint8_t v_skipInstances_boxed_1717_; lean_object* v_res_1718_; 
v_usedLetOnly_boxed_1715_ = lean_unbox(v_usedLetOnly_1705_);
v_skipConstInApp_boxed_1716_ = lean_unbox(v_skipConstInApp_1706_);
v_skipInstances_boxed_1717_ = lean_unbox(v_skipInstances_1707_);
v_res_1718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1701_, v_pre_1702_, v_e_1703_, v_post_1704_, v_usedLetOnly_boxed_1715_, v_skipConstInApp_boxed_1716_, v_skipInstances_boxed_1717_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1708_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1719_, lean_object* v_post_1720_, uint8_t v_usedLetOnly_1721_, uint8_t v_skipConstInApp_1722_, uint8_t v_skipInstances_1723_, lean_object* v_e_1724_, lean_object* v_a_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_inc(v_a_1725_);
v___x_1732_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1732_, 0, lean_box(0));
lean_closure_set(v___x_1732_, 1, lean_box(0));
lean_closure_set(v___x_1732_, 2, v_a_1725_);
v___x_1733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1732_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1788_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1788_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1788_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1787_; 
v_fst_1738_ = lean_ctor_get(v_a_1734_, 0);
v_snd_1739_ = lean_ctor_get(v_a_1734_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_a_1734_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1741_ = v_a_1734_;
v_isShared_1742_ = v_isSharedCheck_1787_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_inc(v_fst_1738_);
lean_dec(v_a_1734_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1787_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1738_, v_e_1724_);
lean_dec(v_fst_1738_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; 
lean_del_object(v___x_1741_);
lean_del_object(v___x_1736_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1745_ = lean_box(v_usedLetOnly_1721_);
v___x_1746_ = lean_box(v_skipConstInApp_1722_);
v___x_1747_ = lean_box(v_skipInstances_1723_);
lean_inc_ref(v_e_1724_);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1748_, 0, v___x_1744_);
lean_closure_set(v___f_1748_, 1, v_pre_1719_);
lean_closure_set(v___f_1748_, 2, v_e_1724_);
lean_closure_set(v___f_1748_, 3, v_post_1720_);
lean_closure_set(v___f_1748_, 4, v___x_1745_);
lean_closure_set(v___f_1748_, 5, v___x_1746_);
lean_closure_set(v___f_1748_, 6, v___x_1747_);
v___x_1749_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1748_, v_a_1725_, v_snd_1739_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v_fst_1751_ = lean_ctor_get(v_a_1750_, 0);
lean_inc_n(v_fst_1751_, 2);
v_snd_1752_ = lean_ctor_get(v_a_1750_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_a_1750_);
lean_inc(v_a_1725_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1753_, 0, v_a_1725_);
lean_closure_set(v___f_1753_, 1, v_e_1724_);
lean_closure_set(v___f_1753_, 2, v_fst_1751_);
v___x_1754_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1753_, v_snd_1752_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1771_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1771_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1771_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_snd_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_snd_1759_ = lean_ctor_get(v_a_1755_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_a_1755_, 0);
lean_dec(v_unused_1770_);
v___x_1761_ = v_a_1755_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_snd_1759_);
lean_dec(v_a_1755_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_fst_1751_);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_fst_1751_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1759_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1764_);
v___x_1766_ = v___x_1757_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_fst_1751_);
v_a_1772_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1754_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1754_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_dec_ref(v_e_1724_);
return v___x_1749_;
}
}
else
{
lean_object* v_val_1780_; lean_object* v___x_1782_; 
lean_dec_ref(v_e_1724_);
lean_dec_ref(v_post_1720_);
lean_dec_ref(v_pre_1719_);
v_val_1780_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1743_, 1);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_val_1780_);
v___x_1782_ = v___x_1741_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_val_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_snd_1739_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1782_);
v___x_1784_ = v___x_1736_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_e_1724_);
lean_dec_ref(v_post_1720_);
lean_dec_ref(v_pre_1719_);
v_a_1789_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1733_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1733_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1797_, lean_object* v_pre_1798_, lean_object* v_post_1799_, lean_object* v_usedLetOnly_1800_, lean_object* v_skipConstInApp_1801_, lean_object* v_skipInstances_1802_, lean_object* v_body_1803_, lean_object* v_x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_usedLetOnly_boxed_1812_; uint8_t v_skipConstInApp_boxed_1813_; uint8_t v_skipInstances_boxed_1814_; lean_object* v_res_1815_; 
v_usedLetOnly_boxed_1812_ = lean_unbox(v_usedLetOnly_1800_);
v_skipConstInApp_boxed_1813_ = lean_unbox(v_skipConstInApp_1801_);
v_skipInstances_boxed_1814_ = lean_unbox(v_skipInstances_1802_);
v_res_1815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1797_, v_pre_1798_, v_post_1799_, v_usedLetOnly_boxed_1812_, v_skipConstInApp_boxed_1813_, v_skipInstances_boxed_1814_, v_body_1803_, v_x_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1805_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1816_, lean_object* v_post_1817_, uint8_t v_usedLetOnly_1818_, uint8_t v_skipConstInApp_1819_, uint8_t v_skipInstances_1820_, lean_object* v_fvars_1821_, lean_object* v_e_1822_, lean_object* v_a_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
if (lean_obj_tag(v_e_1822_) == 7)
{
lean_object* v_binderName_1830_; lean_object* v_binderType_1831_; lean_object* v_body_1832_; uint8_t v_binderInfo_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_binderName_1830_ = lean_ctor_get(v_e_1822_, 0);
lean_inc(v_binderName_1830_);
v_binderType_1831_ = lean_ctor_get(v_e_1822_, 1);
lean_inc_ref(v_binderType_1831_);
v_body_1832_ = lean_ctor_get(v_e_1822_, 2);
lean_inc_ref(v_body_1832_);
v_binderInfo_1833_ = lean_ctor_get_uint8(v_e_1822_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1822_, 3);
v___x_1834_ = lean_expr_instantiate_rev(v_binderType_1831_, v_fvars_1821_);
lean_dec_ref(v_binderType_1831_);
lean_inc_ref(v_post_1817_);
lean_inc_ref(v_pre_1816_);
v___x_1835_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1816_, v_post_1817_, v_usedLetOnly_1818_, v_skipConstInApp_1819_, v_skipInstances_1820_, v___x_1834_, v_a_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___f_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v_fst_1837_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_fst_1837_);
v_snd_1838_ = lean_ctor_get(v_a_1836_, 1);
lean_inc(v_snd_1838_);
lean_dec(v_a_1836_);
v___x_1839_ = lean_box(v_usedLetOnly_1818_);
v___x_1840_ = lean_box(v_skipConstInApp_1819_);
v___x_1841_ = lean_box(v_skipInstances_1820_);
v___f_1842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1842_, 0, v_fvars_1821_);
lean_closure_set(v___f_1842_, 1, v_pre_1816_);
lean_closure_set(v___f_1842_, 2, v_post_1817_);
lean_closure_set(v___f_1842_, 3, v___x_1839_);
lean_closure_set(v___f_1842_, 4, v___x_1840_);
lean_closure_set(v___f_1842_, 5, v___x_1841_);
lean_closure_set(v___f_1842_, 6, v_body_1832_);
v___x_1843_ = 0;
v___x_1844_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1830_, v_binderInfo_1833_, v_fst_1837_, v___f_1842_, v___x_1843_, v_a_1823_, v_snd_1838_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1844_;
}
else
{
lean_dec_ref(v_body_1832_);
lean_dec(v_binderName_1830_);
lean_dec_ref(v_fvars_1821_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_expr_instantiate_rev(v_e_1822_, v_fvars_1821_);
lean_dec_ref(v_e_1822_);
lean_inc_ref(v_post_1817_);
lean_inc_ref(v_pre_1816_);
v___x_1846_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1816_, v_post_1817_, v_usedLetOnly_1818_, v_skipConstInApp_1819_, v_skipInstances_1820_, v___x_1845_, v_a_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_fst_1848_; lean_object* v_snd_1849_; uint8_t v___x_1850_; uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v_fst_1848_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_fst_1848_);
v_snd_1849_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1849_);
lean_dec(v_a_1847_);
v___x_1850_ = 0;
v___x_1851_ = 1;
v___x_1852_ = 1;
v___x_1853_ = l_Lean_Meta_mkForallFVars(v_fvars_1821_, v_fst_1848_, v___x_1850_, v_usedLetOnly_1818_, v___x_1851_, v___x_1852_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec_ref(v_fvars_1821_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1816_, v_post_1817_, v_usedLetOnly_1818_, v_skipConstInApp_1819_, v_skipInstances_1820_, v_a_1854_, v_a_1823_, v_snd_1849_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1855_;
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_snd_1849_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
v_a_1856_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1853_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1853_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1821_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1864_, lean_object* v_pre_1865_, lean_object* v_post_1866_, uint8_t v_usedLetOnly_1867_, uint8_t v_skipConstInApp_1868_, uint8_t v_skipInstances_1869_, lean_object* v_body_1870_, lean_object* v_x_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_array_push(v_fvars_1864_, v_x_1871_);
v___x_1880_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1865_, v_post_1866_, v_usedLetOnly_1867_, v_skipConstInApp_1868_, v_skipInstances_1869_, v___x_1879_, v_body_1870_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1881_, lean_object* v_post_1882_, lean_object* v_usedLetOnly_1883_, lean_object* v_skipConstInApp_1884_, lean_object* v_skipInstances_1885_, lean_object* v_sz_1886_, lean_object* v_i_1887_, lean_object* v_bs_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
uint8_t v_usedLetOnly_boxed_1896_; uint8_t v_skipConstInApp_boxed_1897_; uint8_t v_skipInstances_boxed_1898_; size_t v_sz_boxed_1899_; size_t v_i_boxed_1900_; lean_object* v_res_1901_; 
v_usedLetOnly_boxed_1896_ = lean_unbox(v_usedLetOnly_1883_);
v_skipConstInApp_boxed_1897_ = lean_unbox(v_skipConstInApp_1884_);
v_skipInstances_boxed_1898_ = lean_unbox(v_skipInstances_1885_);
v_sz_boxed_1899_ = lean_unbox_usize(v_sz_1886_);
lean_dec(v_sz_1886_);
v_i_boxed_1900_ = lean_unbox_usize(v_i_1887_);
lean_dec(v_i_1887_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1881_, v_post_1882_, v_usedLetOnly_boxed_1896_, v_skipConstInApp_boxed_1897_, v_skipInstances_boxed_1898_, v_sz_boxed_1899_, v_i_boxed_1900_, v_bs_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1889_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1902_, lean_object* v_post_1903_, lean_object* v_usedLetOnly_1904_, lean_object* v_skipConstInApp_1905_, lean_object* v_skipInstances_1906_, lean_object* v_e_1907_, lean_object* v_a_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v_usedLetOnly_boxed_1915_; uint8_t v_skipConstInApp_boxed_1916_; uint8_t v_skipInstances_boxed_1917_; lean_object* v_res_1918_; 
v_usedLetOnly_boxed_1915_ = lean_unbox(v_usedLetOnly_1904_);
v_skipConstInApp_boxed_1916_ = lean_unbox(v_skipConstInApp_1905_);
v_skipInstances_boxed_1917_ = lean_unbox(v_skipInstances_1906_);
v_res_1918_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1902_, v_post_1903_, v_usedLetOnly_boxed_1915_, v_skipConstInApp_boxed_1916_, v_skipInstances_boxed_1917_, v_e_1907_, v_a_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v_a_1908_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1919_, lean_object* v_post_1920_, lean_object* v_usedLetOnly_1921_, lean_object* v_skipConstInApp_1922_, lean_object* v_skipInstances_1923_, lean_object* v_fvars_1924_, lean_object* v_e_1925_, lean_object* v_a_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v_usedLetOnly_boxed_1933_; uint8_t v_skipConstInApp_boxed_1934_; uint8_t v_skipInstances_boxed_1935_; lean_object* v_res_1936_; 
v_usedLetOnly_boxed_1933_ = lean_unbox(v_usedLetOnly_1921_);
v_skipConstInApp_boxed_1934_ = lean_unbox(v_skipConstInApp_1922_);
v_skipInstances_boxed_1935_ = lean_unbox(v_skipInstances_1923_);
v_res_1936_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1919_, v_post_1920_, v_usedLetOnly_boxed_1933_, v_skipConstInApp_boxed_1934_, v_skipInstances_boxed_1935_, v_fvars_1924_, v_e_1925_, v_a_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v_a_1926_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1937_, lean_object* v_post_1938_, lean_object* v_usedLetOnly_1939_, lean_object* v_skipConstInApp_1940_, lean_object* v_skipInstances_1941_, lean_object* v_fvars_1942_, lean_object* v_e_1943_, lean_object* v_a_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v_usedLetOnly_boxed_1951_; uint8_t v_skipConstInApp_boxed_1952_; uint8_t v_skipInstances_boxed_1953_; lean_object* v_res_1954_; 
v_usedLetOnly_boxed_1951_ = lean_unbox(v_usedLetOnly_1939_);
v_skipConstInApp_boxed_1952_ = lean_unbox(v_skipConstInApp_1940_);
v_skipInstances_boxed_1953_ = lean_unbox(v_skipInstances_1941_);
v_res_1954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1937_, v_post_1938_, v_usedLetOnly_boxed_1951_, v_skipConstInApp_boxed_1952_, v_skipInstances_boxed_1953_, v_fvars_1942_, v_e_1943_, v_a_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v_a_1944_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1955_, lean_object* v_post_1956_, lean_object* v_usedLetOnly_1957_, lean_object* v_skipConstInApp_1958_, lean_object* v_skipInstances_1959_, lean_object* v_e_1960_, lean_object* v_a_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_usedLetOnly_boxed_1968_; uint8_t v_skipConstInApp_boxed_1969_; uint8_t v_skipInstances_boxed_1970_; lean_object* v_res_1971_; 
v_usedLetOnly_boxed_1968_ = lean_unbox(v_usedLetOnly_1957_);
v_skipConstInApp_boxed_1969_ = lean_unbox(v_skipConstInApp_1958_);
v_skipInstances_boxed_1970_ = lean_unbox(v_skipInstances_1959_);
v_res_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1955_, v_post_1956_, v_usedLetOnly_boxed_1968_, v_skipConstInApp_boxed_1969_, v_skipInstances_boxed_1970_, v_e_1960_, v_a_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v_a_1961_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1972_, lean_object* v_post_1973_, lean_object* v_usedLetOnly_1974_, lean_object* v_skipConstInApp_1975_, lean_object* v_skipInstances_1976_, lean_object* v_fvars_1977_, lean_object* v_e_1978_, lean_object* v_a_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v_usedLetOnly_boxed_1986_; uint8_t v_skipConstInApp_boxed_1987_; uint8_t v_skipInstances_boxed_1988_; lean_object* v_res_1989_; 
v_usedLetOnly_boxed_1986_ = lean_unbox(v_usedLetOnly_1974_);
v_skipConstInApp_boxed_1987_ = lean_unbox(v_skipConstInApp_1975_);
v_skipInstances_boxed_1988_ = lean_unbox(v_skipInstances_1976_);
v_res_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1972_, v_post_1973_, v_usedLetOnly_boxed_1986_, v_skipConstInApp_boxed_1987_, v_skipInstances_boxed_1988_, v_fvars_1977_, v_e_1978_, v_a_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v_a_1979_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_1990_, lean_object* v___x_1991_, lean_object* v_pre_1992_, lean_object* v_post_1993_, lean_object* v_usedLetOnly_1994_, lean_object* v_skipConstInApp_1995_, lean_object* v_skipInstances_1996_, lean_object* v_a_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v_usedLetOnly_boxed_2006_; uint8_t v_skipConstInApp_boxed_2007_; uint8_t v_skipInstances_boxed_2008_; lean_object* v_res_2009_; 
v_usedLetOnly_boxed_2006_ = lean_unbox(v_usedLetOnly_1994_);
v_skipConstInApp_boxed_2007_ = lean_unbox(v_skipConstInApp_1995_);
v_skipInstances_boxed_2008_ = lean_unbox(v_skipInstances_1996_);
v_res_2009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1990_, v___x_1991_, v_pre_1992_, v_post_1993_, v_usedLetOnly_boxed_2006_, v_skipConstInApp_boxed_2007_, v_skipInstances_boxed_2008_, v_a_1997_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_1999_);
lean_dec_ref(v___x_1991_);
lean_dec(v_upperBound_1990_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2010_, lean_object* v_pre_2011_, lean_object* v_post_2012_, lean_object* v_usedLetOnly_2013_, lean_object* v_skipConstInApp_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v_skipInstances_boxed_2025_; uint8_t v_usedLetOnly_boxed_2026_; uint8_t v_skipConstInApp_boxed_2027_; lean_object* v_res_2028_; 
v_skipInstances_boxed_2025_ = lean_unbox(v_skipInstances_2010_);
v_usedLetOnly_boxed_2026_ = lean_unbox(v_usedLetOnly_2013_);
v_skipConstInApp_boxed_2027_ = lean_unbox(v_skipConstInApp_2014_);
v_res_2028_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2025_, v_pre_2011_, v_post_2012_, v_usedLetOnly_boxed_2026_, v_skipConstInApp_boxed_2027_, v_x_2015_, v_x_2016_, v_x_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2018_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_apply_1(v_x_2030_, lean_box(0));
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___y_2031_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_x_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2040_, v_x_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2048_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_unsigned_to_nat(16u);
v___x_2051_ = lean_mk_array(v___x_2050_, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___x_2052_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2056_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2056_, 0, lean_box(0));
lean_closure_set(v___x_2056_, 1, lean_box(0));
lean_closure_set(v___x_2056_, 2, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2057_, lean_object* v_pre_2058_, lean_object* v_post_2059_, uint8_t v_usedLetOnly_2060_, uint8_t v_skipConstInApp_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_a_2070_; lean_object* v_fst_2071_; lean_object* v_snd_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2068_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2069_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2068_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
v_fst_2071_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_fst_2071_);
v_snd_2072_ = lean_ctor_get(v_a_2070_, 1);
lean_inc(v_snd_2072_);
lean_dec(v_a_2070_);
v___x_2073_ = 0;
v___x_2074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2058_, v_post_2059_, v_usedLetOnly_2060_, v_skipConstInApp_2061_, v___x_2073_, v_input_2057_, v_fst_2071_, v_snd_2072_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2096_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v_fst_2076_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_fst_2076_);
v_snd_2077_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_snd_2077_);
lean_dec(v_a_2075_);
v___x_2078_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2078_, 0, lean_box(0));
lean_closure_set(v___x_2078_, 1, lean_box(0));
lean_closure_set(v___x_2078_, 2, v_fst_2071_);
v___x_2079_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2078_, v_snd_2077_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2096_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2096_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2094_; 
v_snd_2084_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_a_2080_, 0);
lean_dec(v_unused_2095_);
v___x_2086_ = v_a_2080_;
v_isShared_2087_ = v_isSharedCheck_2094_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_dec(v_a_2080_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2094_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_fst_2076_);
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_fst_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_snd_2084_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2089_);
v___x_2091_ = v___x_2082_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_dec(v_fst_2071_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2097_, lean_object* v_pre_2098_, lean_object* v_post_2099_, lean_object* v_usedLetOnly_2100_, lean_object* v_skipConstInApp_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v_usedLetOnly_boxed_2108_; uint8_t v_skipConstInApp_boxed_2109_; lean_object* v_res_2110_; 
v_usedLetOnly_boxed_2108_ = lean_unbox(v_usedLetOnly_2100_);
v_skipConstInApp_boxed_2109_ = lean_unbox(v_skipConstInApp_2101_);
v_res_2110_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2097_, v_pre_2098_, v_post_2099_, v_usedLetOnly_boxed_2108_, v_skipConstInApp_boxed_2109_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___y_2120_; lean_object* v___x_2137_; uint8_t v_transparency_2138_; lean_object* v___f_2139_; lean_object* v___f_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2137_ = l_Lean_Meta_Context_config(v_a_2114_);
v_transparency_2138_ = lean_ctor_get_uint8(v___x_2137_, 9);
lean_dec_ref(v___x_2137_);
v___f_2139_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2140_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2141_ = 0;
v___x_2142_ = 3;
v___x_2143_ = lean_box(0);
v___x_2144_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2138_, v___x_2142_);
if (v___x_2144_ == 0)
{
lean_object* v_keyedConfig_2145_; uint8_t v_trackZetaDelta_2146_; lean_object* v_zetaDeltaSet_2147_; lean_object* v_lctx_2148_; lean_object* v_localInstances_2149_; lean_object* v_defEqCtx_x3f_2150_; lean_object* v_synthPendingDepth_2151_; lean_object* v_customCanUnfoldPredicate_x3f_2152_; uint8_t v_univApprox_2153_; uint8_t v_inTypeClassResolution_2154_; uint8_t v_cacheInferType_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_keyedConfig_2145_ = lean_ctor_get(v_a_2114_, 0);
v_trackZetaDelta_2146_ = lean_ctor_get_uint8(v_a_2114_, sizeof(void*)*7);
v_zetaDeltaSet_2147_ = lean_ctor_get(v_a_2114_, 1);
v_lctx_2148_ = lean_ctor_get(v_a_2114_, 2);
v_localInstances_2149_ = lean_ctor_get(v_a_2114_, 3);
v_defEqCtx_x3f_2150_ = lean_ctor_get(v_a_2114_, 4);
v_synthPendingDepth_2151_ = lean_ctor_get(v_a_2114_, 5);
v_customCanUnfoldPredicate_x3f_2152_ = lean_ctor_get(v_a_2114_, 6);
v_univApprox_2153_ = lean_ctor_get_uint8(v_a_2114_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2154_ = lean_ctor_get_uint8(v_a_2114_, sizeof(void*)*7 + 2);
v_cacheInferType_2155_ = lean_ctor_get_uint8(v_a_2114_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2145_);
v___x_2156_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2142_, v_keyedConfig_2145_);
lean_inc(v_customCanUnfoldPredicate_x3f_2152_);
lean_inc(v_synthPendingDepth_2151_);
lean_inc(v_defEqCtx_x3f_2150_);
lean_inc_ref(v_localInstances_2149_);
lean_inc_ref(v_lctx_2148_);
lean_inc(v_zetaDeltaSet_2147_);
v___x_2157_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v_zetaDeltaSet_2147_);
lean_ctor_set(v___x_2157_, 2, v_lctx_2148_);
lean_ctor_set(v___x_2157_, 3, v_localInstances_2149_);
lean_ctor_set(v___x_2157_, 4, v_defEqCtx_x3f_2150_);
lean_ctor_set(v___x_2157_, 5, v_synthPendingDepth_2151_);
lean_ctor_set(v___x_2157_, 6, v_customCanUnfoldPredicate_x3f_2152_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*7, v_trackZetaDelta_2146_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*7 + 1, v_univApprox_2153_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2154_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*7 + 3, v_cacheInferType_2155_);
v___x_2158_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2113_, v___f_2140_, v___f_2139_, v___x_2141_, v___x_2141_, v___x_2143_, v___x_2157_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec_ref_known(v___x_2157_, 7);
v___y_2120_ = v___x_2158_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2113_, v___f_2140_, v___f_2139_, v___x_2141_, v___x_2141_, v___x_2143_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
v___y_2120_ = v___x_2159_;
goto v___jp_2119_;
}
v___jp_2119_:
{
if (lean_obj_tag(v___y_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___y_2120_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___y_2120_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___y_2120_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___y_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___y_2120_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___y_2120_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___y_2120_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___y_2120_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_expandCoe(v_e_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2167_, lean_object* v_m_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2168_, v_a_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2171_, lean_object* v_m_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2171_, v_m_2172_, v_a_2173_);
lean_dec(v_a_2173_);
lean_dec_ref(v_m_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2176_, v_x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2179_, v_x_2180_, v_x_2181_);
lean_dec_ref(v_x_2181_);
lean_dec_ref(v_x_2180_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2184_, lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2185_, v_x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2188_, lean_object* v_a_2189_, lean_object* v_x_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2188_, v_a_2189_, v_x_2190_);
lean_dec(v_x_2190_);
lean_dec(v_a_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2192_, lean_object* v___x_2193_, lean_object* v_pre_2194_, lean_object* v_post_2195_, uint8_t v_usedLetOnly_2196_, uint8_t v_skipConstInApp_2197_, uint8_t v_skipInstances_2198_, lean_object* v___x_2199_, lean_object* v_inst_2200_, lean_object* v_R_2201_, lean_object* v_a_2202_, lean_object* v_b_2203_, lean_object* v_c_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2192_, v___x_2193_, v_pre_2194_, v_post_2195_, v_usedLetOnly_2196_, v_skipConstInApp_2197_, v_skipInstances_2198_, v_a_2202_, v_b_2203_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2213_ = _args[0];
lean_object* v___x_2214_ = _args[1];
lean_object* v_pre_2215_ = _args[2];
lean_object* v_post_2216_ = _args[3];
lean_object* v_usedLetOnly_2217_ = _args[4];
lean_object* v_skipConstInApp_2218_ = _args[5];
lean_object* v_skipInstances_2219_ = _args[6];
lean_object* v___x_2220_ = _args[7];
lean_object* v_inst_2221_ = _args[8];
lean_object* v_R_2222_ = _args[9];
lean_object* v_a_2223_ = _args[10];
lean_object* v_b_2224_ = _args[11];
lean_object* v_c_2225_ = _args[12];
lean_object* v___y_2226_ = _args[13];
lean_object* v___y_2227_ = _args[14];
lean_object* v___y_2228_ = _args[15];
lean_object* v___y_2229_ = _args[16];
lean_object* v___y_2230_ = _args[17];
lean_object* v___y_2231_ = _args[18];
lean_object* v___y_2232_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2233_; uint8_t v_skipConstInApp_boxed_2234_; uint8_t v_skipInstances_boxed_2235_; lean_object* v_res_2236_; 
v_usedLetOnly_boxed_2233_ = lean_unbox(v_usedLetOnly_2217_);
v_skipConstInApp_boxed_2234_ = lean_unbox(v_skipConstInApp_2218_);
v_skipInstances_boxed_2235_ = lean_unbox(v_skipInstances_2219_);
v_res_2236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2213_, v___x_2214_, v_pre_2215_, v_post_2216_, v_usedLetOnly_boxed_2233_, v_skipConstInApp_boxed_2234_, v_skipInstances_boxed_2235_, v___x_2220_, v_inst_2221_, v_R_2222_, v_a_2223_, v_b_2224_, v_c_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2226_);
lean_dec(v___x_2220_);
lean_dec_ref(v___x_2214_);
lean_dec(v_upperBound_2213_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2237_, lean_object* v_m_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2238_, v_a_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_m_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2241_, v_m_2242_, v_a_2243_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v_m_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2245_, lean_object* v_name_2246_, uint8_t v_bi_2247_, lean_object* v_type_2248_, lean_object* v_k_2249_, uint8_t v_kind_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2246_, v_bi_2247_, v_type_2248_, v_k_2249_, v_kind_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2259_, lean_object* v_name_2260_, lean_object* v_bi_2261_, lean_object* v_type_2262_, lean_object* v_k_2263_, lean_object* v_kind_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_bi_boxed_2272_; uint8_t v_kind_boxed_2273_; lean_object* v_res_2274_; 
v_bi_boxed_2272_ = lean_unbox(v_bi_2261_);
v_kind_boxed_2273_ = lean_unbox(v_kind_2264_);
v_res_2274_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2259_, v_name_2260_, v_bi_boxed_2272_, v_type_2262_, v_k_2263_, v_kind_boxed_2273_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2275_, lean_object* v_name_2276_, lean_object* v_type_2277_, lean_object* v_val_2278_, lean_object* v_k_2279_, uint8_t v_nondep_2280_, uint8_t v_kind_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2276_, v_type_2277_, v_val_2278_, v_k_2279_, v_nondep_2280_, v_kind_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_name_2291_, lean_object* v_type_2292_, lean_object* v_val_2293_, lean_object* v_k_2294_, lean_object* v_nondep_2295_, lean_object* v_kind_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
uint8_t v_nondep_boxed_2304_; uint8_t v_kind_boxed_2305_; lean_object* v_res_2306_; 
v_nondep_boxed_2304_ = lean_unbox(v_nondep_2295_);
v_kind_boxed_2305_ = lean_unbox(v_kind_2296_);
v_res_2306_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2290_, v_name_2291_, v_type_2292_, v_val_2293_, v_k_2294_, v_nondep_boxed_2304_, v_kind_boxed_2305_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2297_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2307_, lean_object* v_ref_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2308_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2315_, lean_object* v_ref_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2315_, v_ref_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2333_, lean_object* v_x_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2333_, v_x_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2335_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2343_, lean_object* v_m_2344_, lean_object* v_a_2345_, lean_object* v_b_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2344_, v_a_2345_, v_b_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2348_, lean_object* v_x_2349_, size_t v_x_2350_, lean_object* v_x_2351_){
_start:
{
uint8_t v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2349_, v_x_2350_, v_x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_){
_start:
{
size_t v_x_39033__boxed_2357_; uint8_t v_res_2358_; lean_object* v_r_2359_; 
v_x_39033__boxed_2357_ = lean_unbox_usize(v_x_2355_);
lean_dec(v_x_2355_);
v_res_2358_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2353_, v_x_2354_, v_x_39033__boxed_2357_, v_x_2356_);
lean_dec_ref(v_x_2356_);
lean_dec_ref(v_x_2354_);
v_r_2359_ = lean_box(v_res_2358_);
return v_r_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2360_, lean_object* v_a_2361_, lean_object* v_x_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2361_, v_x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_a_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2364_, v_a_2365_, v_x_2366_);
lean_dec(v_x_2366_);
lean_dec_ref(v_a_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2368_, lean_object* v_a_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_a_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2372_, v_a_2373_, v_x_2374_);
lean_dec(v_x_2374_);
lean_dec_ref(v_a_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2377_, lean_object* v_data_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2380_, lean_object* v_a_2381_, lean_object* v_b_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2381_, v_b_2382_, v_x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2385_, lean_object* v_keys_2386_, lean_object* v_vals_2387_, lean_object* v_heq_2388_, lean_object* v_i_2389_, lean_object* v_k_2390_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2386_, v_i_2389_, v_k_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2392_, lean_object* v_keys_2393_, lean_object* v_vals_2394_, lean_object* v_heq_2395_, lean_object* v_i_2396_, lean_object* v_k_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2392_, v_keys_2393_, v_vals_2394_, v_heq_2395_, v_i_2396_, v_k_2397_);
lean_dec_ref(v_k_2397_);
lean_dec_ref(v_vals_2394_);
lean_dec_ref(v_keys_2393_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2400_, lean_object* v_i_2401_, lean_object* v_source_2402_, lean_object* v_target_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2401_, v_source_2402_, v_target_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2406_, v_x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2409_, lean_object* v_decl_2410_, lean_object* v_ref_2411_){
_start:
{
lean_object* v_defValue_2413_; lean_object* v_descr_2414_; lean_object* v_deprecation_x3f_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_defValue_2413_ = lean_ctor_get(v_decl_2410_, 0);
v_descr_2414_ = lean_ctor_get(v_decl_2410_, 1);
v_deprecation_x3f_2415_ = lean_ctor_get(v_decl_2410_, 2);
v___x_2416_ = lean_alloc_ctor(1, 0, 1);
v___x_2417_ = lean_unbox(v_defValue_2413_);
lean_ctor_set_uint8(v___x_2416_, 0, v___x_2417_);
lean_inc(v_deprecation_x3f_2415_);
lean_inc_ref(v_descr_2414_);
lean_inc_n(v_name_2409_, 2);
v___x_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2418_, 0, v_name_2409_);
lean_ctor_set(v___x_2418_, 1, v_ref_2411_);
lean_ctor_set(v___x_2418_, 2, v___x_2416_);
lean_ctor_set(v___x_2418_, 3, v_descr_2414_);
lean_ctor_set(v___x_2418_, 4, v_deprecation_x3f_2415_);
v___x_2419_ = lean_register_option(v_name_2409_, v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2428_);
v___x_2421_ = v___x_2419_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_inc(v_defValue_2413_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_name_2409_);
lean_ctor_set(v___x_2423_, 1, v_defValue_2413_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_name_2409_);
v_a_2429_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2419_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2419_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2437_, lean_object* v_decl_2438_, lean_object* v_ref_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2437_, v_decl_2438_, v_ref_2439_);
lean_dec_ref(v_decl_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2457_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2458_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2459_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2456_, v___x_2457_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_ref_2468_; lean_object* v___x_2469_; lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2478_; 
v_ref_2468_ = lean_ctor_get(v___y_2465_, 2);
v___x_2469_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2478_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_inc(v_ref_2468_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_ref_2468_);
lean_ctor_set(v___x_2474_, 1, v_a_2470_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 1);
lean_ctor_set(v___x_2472_, 0, v___x_2474_);
v___x_2476_ = v___x_2472_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2485_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2494_ = l_Lean_stringToMessageData(v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2501_, lean_object* v_expectedType_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; 
lean_inc(v_a_2506_);
lean_inc_ref(v_a_2505_);
lean_inc(v_a_2504_);
lean_inc_ref(v_a_2503_);
lean_inc_ref(v_expr_2501_);
v___x_2508_ = lean_infer_type(v_expr_2501_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2510_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc_n(v_a_2509_, 2);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = l_Lean_Meta_getLevel(v_a_2509_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2512_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
lean_inc_ref(v_expectedType_2502_);
v___x_2512_ = l_Lean_Meta_getLevel(v_expectedType_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2513_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2511_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
lean_inc_ref(v___x_2517_);
v___x_2518_ = l_Lean_mkConst(v___x_2514_, v___x_2517_);
v___x_2519_ = lean_unsigned_to_nat(3u);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2519_);
lean_inc(v_a_2509_);
v___x_2521_ = lean_array_push(v___x_2520_, v_a_2509_);
lean_inc_ref(v_expr_2501_);
v___x_2522_ = lean_array_push(v___x_2521_, v_expr_2501_);
lean_inc_ref(v_expectedType_2502_);
v___x_2523_ = lean_array_push(v___x_2522_, v_expectedType_2502_);
v___x_2524_ = l_Lean_mkAppN(v___x_2518_, v___x_2523_);
lean_dec_ref(v___x_2523_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Lean_Meta_trySynthInstance(v___x_2524_, v___x_2525_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2624_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2624_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2624_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
switch(lean_obj_tag(v_a_2527_))
{
case 0:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
lean_dec_ref_known(v___x_2517_, 2);
lean_dec(v_a_2509_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v___x_2531_ = lean_box(0);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
case 1:
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2619_; 
lean_del_object(v___x_2529_);
v_a_2535_ = lean_ctor_get(v_a_2527_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2527_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2537_ = v_a_2527_;
v_isShared_2538_ = v_isSharedCheck_2619_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v_a_2527_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2619_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2539_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2540_ = l_Lean_mkConst(v___x_2539_, v___x_2517_);
v___x_2541_ = lean_unsigned_to_nat(4u);
v___x_2542_ = lean_mk_empty_array_with_capacity(v___x_2541_);
v___x_2543_ = lean_array_push(v___x_2542_, v_a_2509_);
lean_inc_ref(v_expr_2501_);
v___x_2544_ = lean_array_push(v___x_2543_, v_expr_2501_);
lean_inc_ref(v_expectedType_2502_);
v___x_2545_ = lean_array_push(v___x_2544_, v_expectedType_2502_);
v___x_2546_ = lean_array_push(v___x_2545_, v_a_2535_);
v___x_2547_ = l_Lean_mkAppN(v___x_2540_, v___x_2546_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l_Lean_Meta_expandCoe(v___x_2547_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2610_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2610_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2610_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2560_; lean_object* v___x_2561_; 
v_fst_2560_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_a_2506_);
lean_inc_ref(v_a_2505_);
lean_inc(v_a_2504_);
lean_inc_ref(v_a_2503_);
lean_inc(v_fst_2560_);
v___x_2561_ = lean_infer_type(v_fst_2560_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
lean_inc_ref(v_expectedType_2502_);
v___x_2563_ = l_Lean_Meta_isExprDefEq(v_a_2562_, v_expectedType_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; uint8_t v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = lean_unbox(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2591_; 
lean_inc(v_fst_2560_);
lean_del_object(v___x_2551_);
lean_del_object(v___x_2537_);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; lean_object* v_unused_2593_; 
v_unused_2592_ = lean_ctor_get(v_a_2549_, 1);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_a_2549_, 0);
lean_dec(v_unused_2593_);
v___x_2567_ = v_a_2549_;
v_isShared_2568_ = v_isSharedCheck_2591_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v_a_2549_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2591_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2569_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2570_ = l_Lean_indentExpr(v_expr_2501_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 7);
lean_ctor_set(v___x_2567_, 1, v___x_2570_);
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v___x_2573_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_indentExpr(v_expectedType_2502_);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_indentExpr(v_fst_2560_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2580_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_del_object(v___x_2551_);
lean_dec(v_a_2549_);
lean_del_object(v___x_2537_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2594_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2563_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2563_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_del_object(v___x_2551_);
lean_dec(v_a_2549_);
lean_del_object(v___x_2537_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2602_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2561_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2561_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
v___jp_2553_:
{
lean_object* v___x_2555_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v_a_2549_);
v___x_2555_ = v___x_2537_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2549_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2555_);
v___x_2557_ = v___x_2551_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2537_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2611_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2548_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2548_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
default: 
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_dec_ref_known(v___x_2517_, 2);
lean_dec(v_a_2509_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v___x_2620_ = lean_box(2);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2620_);
v___x_2622_ = v___x_2529_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v___x_2517_, 2);
lean_dec(v_a_2509_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2625_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2526_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2526_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2511_);
lean_dec(v_a_2509_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2633_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2512_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2512_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2641_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2510_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2510_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_expectedType_2502_);
lean_dec_ref(v_expr_2501_);
v_a_2649_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2508_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2508_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2657_, lean_object* v_expectedType_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2657_, v_expectedType_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_msg_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2673_, v_msg_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2681_, lean_object* v_expectedType_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2681_, v_expectedType_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2713_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2713_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2713_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
switch(lean_obj_tag(v_a_2689_))
{
case 0:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2693_ = lean_box(0);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2693_);
v___x_2695_ = v___x_2691_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
case 1:
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2708_; 
v_a_2697_ = lean_ctor_get(v_a_2689_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_a_2689_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2699_ = v_a_2689_;
v_isShared_2700_ = v_isSharedCheck_2708_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v_a_2689_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2708_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_fst_2701_; lean_object* v___x_2703_; 
v_fst_2701_ = lean_ctor_get(v_a_2697_, 0);
lean_inc(v_fst_2701_);
lean_dec(v_a_2697_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_fst_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_fst_2701_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2703_);
v___x_2705_ = v___x_2691_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
default: 
{
lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(2);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2709_);
v___x_2711_ = v___x_2691_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
v_a_2714_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2688_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2688_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2722_, lean_object* v_expectedType_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2722_, v_expectedType_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
return v_res_2729_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2741_ = l_Lean_stringToMessageData(v___x_2740_);
return v___x_2741_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2751_; 
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
lean_inc_ref(v_a_2746_);
lean_inc_ref(v_expr_2745_);
v___x_2751_ = lean_infer_type(v_expr_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2753_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_n(v_a_2752_, 2);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2753_ = l_Lean_Meta_getLevel(v_a_2752_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_n(v_a_2756_, 2);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = l_Lean_mkSort(v_a_2756_);
lean_inc(v_a_2752_);
v___x_2758_ = l_Lean_mkArrow(v_a_2752_, v___x_2757_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2759_);
v___x_2761_ = 0;
v___x_2762_ = lean_box(0);
v___x_2763_ = l_Lean_Meta_mkFreshExprMVar(v___x_2760_, v___x_2761_, v___x_2762_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc_n(v_a_2764_, 2);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2756_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_a_2754_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
lean_inc_ref(v___x_2768_);
v___x_2769_ = l_Lean_Expr_const___override(v___x_2765_, v___x_2768_);
lean_inc(v_a_2752_);
v___x_2770_ = l_Lean_mkAppB(v___x_2769_, v_a_2752_, v_a_2764_);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Lean_Meta_trySynthInstance(v___x_2770_, v___x_2771_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2859_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2859_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2859_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
if (lean_obj_tag(v_a_2773_) == 1)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2855_; 
lean_del_object(v___x_2775_);
v_a_2777_ = lean_ctor_get(v_a_2773_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_a_2773_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2779_ = v_a_2773_;
v_isShared_2780_ = v_isSharedCheck_2855_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v_a_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2855_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2781_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2782_ = l_Lean_Expr_const___override(v___x_2781_, v___x_2768_);
lean_inc_ref(v_expr_2745_);
lean_inc(v_a_2777_);
v___x_2783_ = l_Lean_mkApp4(v___x_2782_, v_a_2752_, v_a_2764_, v_a_2777_, v_expr_2745_);
v___x_2784_ = l_Lean_Meta_expandCoe(v___x_2783_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2846_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2846_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2846_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_fst_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2844_; 
v_fst_2789_ = lean_ctor_get(v_a_2785_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_a_2785_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v_a_2785_, 1);
lean_dec(v_unused_2845_);
v___x_2791_ = v_a_2785_;
v_isShared_2792_ = v_isSharedCheck_2844_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_fst_2789_);
lean_dec(v_a_2785_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2844_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2800_; 
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
lean_inc_ref(v_a_2746_);
lean_inc(v_fst_2789_);
v___x_2800_ = lean_infer_type(v_fst_2789_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
lean_inc_ref(v_a_2746_);
v___x_2802_ = lean_whnf(v_a_2801_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; uint8_t v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = l_Lean_Expr_isForall(v_a_2803_);
lean_dec(v_a_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_del_object(v___x_2787_);
lean_del_object(v___x_2779_);
v___x_2805_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2806_ = l_Lean_indentExpr(v_expr_2745_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 7);
lean_ctor_set(v___x_2791_, 1, v___x_2806_);
lean_ctor_set(v___x_2791_, 0, v___x_2805_);
v___x_2808_ = v___x_2791_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v___x_2809_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_indentExpr(v_fst_2789_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2814_ = l_Lean_indentExpr(v_a_2777_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_MessageData_hint_x27(v___x_2815_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2812_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2817_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_del_object(v___x_2791_);
lean_dec(v_a_2777_);
lean_dec_ref(v_expr_2745_);
goto v___jp_2793_;
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_del_object(v___x_2779_);
lean_dec(v_a_2777_);
lean_dec_ref(v_expr_2745_);
v_a_2828_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2802_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2802_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_del_object(v___x_2779_);
lean_dec(v_a_2777_);
lean_dec_ref(v_expr_2745_);
v_a_2836_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2800_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2800_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
v___jp_2793_:
{
lean_object* v___x_2795_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_fst_2789_);
v___x_2795_ = v___x_2779_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_fst_2789_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2795_);
v___x_2797_ = v___x_2787_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2779_);
lean_dec(v_a_2777_);
lean_dec_ref(v_expr_2745_);
v_a_2847_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2784_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2784_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
else
{
lean_object* v___x_2857_; 
lean_dec(v_a_2773_);
lean_dec_ref_known(v___x_2768_, 2);
lean_dec(v_a_2764_);
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2771_);
v___x_2857_ = v___x_2775_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2771_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref_known(v___x_2768_, 2);
lean_dec(v_a_2764_);
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
v_a_2860_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2772_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2772_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_a_2756_);
lean_dec(v_a_2754_);
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
v_a_2868_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2763_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2763_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_a_2756_);
lean_dec(v_a_2754_);
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
v_a_2876_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2758_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2758_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_a_2754_);
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
v_a_2884_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2755_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2755_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_a_2752_);
lean_dec_ref(v_expr_2745_);
v_a_2892_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2753_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2753_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_expr_2745_);
v_a_2900_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2751_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2751_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2914_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2923_ = l_Lean_stringToMessageData(v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2926_ = l_Lean_stringToMessageData(v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2933_; 
lean_inc(v_a_2931_);
lean_inc_ref(v_a_2930_);
lean_inc(v_a_2929_);
lean_inc_ref(v_a_2928_);
lean_inc_ref(v_expr_2927_);
v___x_2933_ = lean_infer_type(v_expr_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc_n(v_a_2934_, 2);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = l_Lean_Meta_getLevel(v_a_2934_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc_n(v_a_2938_, 2);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = l_Lean_mkSort(v_a_2938_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
v___x_2941_ = 0;
v___x_2942_ = lean_box(0);
v___x_2943_ = l_Lean_Meta_mkFreshExprMVar(v___x_2940_, v___x_2941_, v___x_2942_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_n(v_a_2944_, 2);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2947_, 0, v_a_2938_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2936_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
lean_inc_ref(v___x_2948_);
v___x_2949_ = l_Lean_Expr_const___override(v___x_2945_, v___x_2948_);
lean_inc(v_a_2934_);
v___x_2950_ = l_Lean_mkAppB(v___x_2949_, v_a_2934_, v_a_2944_);
v___x_2951_ = lean_box(0);
v___x_2952_ = l_Lean_Meta_trySynthInstance(v___x_2950_, v___x_2951_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3039_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3039_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3039_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
if (lean_obj_tag(v_a_2953_) == 1)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3035_; 
lean_del_object(v___x_2955_);
v_a_2957_ = lean_ctor_get(v_a_2953_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2959_ = v_a_2953_;
v_isShared_2960_ = v_isSharedCheck_3035_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v_a_2953_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3035_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2961_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2962_ = l_Lean_Expr_const___override(v___x_2961_, v___x_2948_);
lean_inc_ref(v_expr_2927_);
lean_inc(v_a_2957_);
v___x_2963_ = l_Lean_mkApp4(v___x_2962_, v_a_2934_, v_a_2944_, v_a_2957_, v_expr_2927_);
v___x_2964_ = l_Lean_Meta_expandCoe(v___x_2963_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3026_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_3026_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3026_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v_fst_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3024_; 
v_fst_2969_ = lean_ctor_get(v_a_2965_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_a_2965_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v_a_2965_, 1);
lean_dec(v_unused_3025_);
v___x_2971_ = v_a_2965_;
v_isShared_2972_ = v_isSharedCheck_3024_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_fst_2969_);
lean_dec(v_a_2965_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3024_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2980_; 
lean_inc(v_a_2931_);
lean_inc_ref(v_a_2930_);
lean_inc(v_a_2929_);
lean_inc_ref(v_a_2928_);
lean_inc(v_fst_2969_);
v___x_2980_ = lean_infer_type(v_fst_2969_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
lean_inc(v_a_2931_);
lean_inc_ref(v_a_2930_);
lean_inc(v_a_2929_);
lean_inc_ref(v_a_2928_);
v___x_2982_ = lean_whnf(v_a_2981_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; uint8_t v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = l_Lean_Expr_isSort(v_a_2983_);
lean_dec(v_a_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
lean_del_object(v___x_2967_);
lean_del_object(v___x_2959_);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2986_ = l_Lean_indentExpr(v_expr_2927_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 7);
lean_ctor_set(v___x_2971_, 1, v___x_2986_);
lean_ctor_set(v___x_2971_, 0, v___x_2985_);
v___x_2988_ = v___x_2971_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v___x_2989_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = l_Lean_indentExpr(v_fst_2969_);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_2994_ = l_Lean_indentExpr(v_a_2957_);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Lean_MessageData_hint_x27(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2992_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2997_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
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
lean_del_object(v___x_2971_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2927_);
goto v___jp_2973_;
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_del_object(v___x_2971_);
lean_dec(v_fst_2969_);
lean_del_object(v___x_2967_);
lean_del_object(v___x_2959_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2927_);
v_a_3008_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2982_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2982_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_del_object(v___x_2971_);
lean_dec(v_fst_2969_);
lean_del_object(v___x_2967_);
lean_del_object(v___x_2959_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2927_);
v_a_3016_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2980_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2980_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
v___jp_2973_:
{
lean_object* v___x_2975_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v_fst_2969_);
v___x_2975_ = v___x_2959_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2969_);
v___x_2975_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2975_);
v___x_2977_ = v___x_2967_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_2959_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2927_);
v_a_3027_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2964_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2964_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v___x_3037_; 
lean_dec(v_a_2953_);
lean_dec_ref_known(v___x_2948_, 2);
lean_dec(v_a_2944_);
lean_dec(v_a_2934_);
lean_dec_ref(v_expr_2927_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2951_);
v___x_3037_ = v___x_2955_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_2951_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref_known(v___x_2948_, 2);
lean_dec(v_a_2944_);
lean_dec(v_a_2934_);
lean_dec_ref(v_expr_2927_);
v_a_3040_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2952_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2952_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_2938_);
lean_dec(v_a_2936_);
lean_dec(v_a_2934_);
lean_dec_ref(v_expr_2927_);
v_a_3048_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2943_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2943_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_a_2936_);
lean_dec(v_a_2934_);
lean_dec_ref(v_expr_2927_);
v_a_3056_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2937_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2937_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_2934_);
lean_dec_ref(v_expr_2927_);
v_a_3064_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2935_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2935_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v_expr_2927_);
v_a_3072_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2933_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_2933_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3087_, lean_object* v___y_3088_){
_start:
{
uint8_t v___x_3090_; 
v___x_3090_ = l_Lean_Expr_hasMVar(v_e_3087_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_e_3087_);
return v___x_3091_;
}
else
{
lean_object* v___x_3092_; lean_object* v_mctx_3093_; lean_object* v___x_3094_; lean_object* v_fst_3095_; lean_object* v_snd_3096_; lean_object* v___x_3097_; lean_object* v_cache_3098_; lean_object* v_zetaDeltaFVarIds_3099_; lean_object* v_postponed_3100_; lean_object* v_diag_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3110_; 
v___x_3092_ = lean_st_ref_get(v___y_3088_);
v_mctx_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_ref(v_mctx_3093_);
lean_dec(v___x_3092_);
v___x_3094_ = l_Lean_instantiateMVarsCore(v_mctx_3093_, v_e_3087_);
v_fst_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_fst_3095_);
v_snd_3096_ = lean_ctor_get(v___x_3094_, 1);
lean_inc(v_snd_3096_);
lean_dec_ref(v___x_3094_);
v___x_3097_ = lean_st_ref_take(v___y_3088_);
v_cache_3098_ = lean_ctor_get(v___x_3097_, 1);
v_zetaDeltaFVarIds_3099_ = lean_ctor_get(v___x_3097_, 2);
v_postponed_3100_ = lean_ctor_get(v___x_3097_, 3);
v_diag_3101_ = lean_ctor_get(v___x_3097_, 4);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3111_);
v___x_3103_ = v___x_3097_;
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_diag_3101_);
lean_inc(v_postponed_3100_);
lean_inc(v_zetaDeltaFVarIds_3099_);
lean_inc(v_cache_3098_);
lean_dec(v___x_3097_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v_snd_3096_);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_snd_3096_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_cache_3098_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_zetaDeltaFVarIds_3099_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_postponed_3100_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_diag_3101_);
v___x_3106_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_st_ref_put(v___y_3088_, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_fst_3095_);
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3112_, v___y_3113_);
lean_dec(v___y_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3116_, v___y_3118_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___y_3137_; lean_object* v___x_3176_; uint8_t v_transparency_3177_; uint8_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3176_ = l_Lean_Meta_Context_config(v_a_3131_);
v_transparency_3177_ = lean_ctor_get_uint8(v___x_3176_, 9);
lean_dec_ref(v___x_3176_);
v___x_3178_ = 2;
v___x_3179_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3177_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v_keyedConfig_3180_; uint8_t v_trackZetaDelta_3181_; lean_object* v_zetaDeltaSet_3182_; lean_object* v_lctx_3183_; lean_object* v_localInstances_3184_; lean_object* v_defEqCtx_x3f_3185_; lean_object* v_synthPendingDepth_3186_; lean_object* v_customCanUnfoldPredicate_x3f_3187_; uint8_t v_univApprox_3188_; uint8_t v_inTypeClassResolution_3189_; uint8_t v_cacheInferType_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_keyedConfig_3180_ = lean_ctor_get(v_a_3131_, 0);
v_trackZetaDelta_3181_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7);
v_zetaDeltaSet_3182_ = lean_ctor_get(v_a_3131_, 1);
v_lctx_3183_ = lean_ctor_get(v_a_3131_, 2);
v_localInstances_3184_ = lean_ctor_get(v_a_3131_, 3);
v_defEqCtx_x3f_3185_ = lean_ctor_get(v_a_3131_, 4);
v_synthPendingDepth_3186_ = lean_ctor_get(v_a_3131_, 5);
v_customCanUnfoldPredicate_x3f_3187_ = lean_ctor_get(v_a_3131_, 6);
v_univApprox_3188_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3189_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 2);
v_cacheInferType_3190_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3180_);
v___x_3191_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3178_, v_keyedConfig_3180_);
lean_inc(v_customCanUnfoldPredicate_x3f_3187_);
lean_inc(v_synthPendingDepth_3186_);
lean_inc(v_defEqCtx_x3f_3185_);
lean_inc_ref(v_localInstances_3184_);
lean_inc_ref(v_lctx_3183_);
lean_inc(v_zetaDeltaSet_3182_);
v___x_3192_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_zetaDeltaSet_3182_);
lean_ctor_set(v___x_3192_, 2, v_lctx_3183_);
lean_ctor_set(v___x_3192_, 3, v_localInstances_3184_);
lean_ctor_set(v___x_3192_, 4, v_defEqCtx_x3f_3185_);
lean_ctor_set(v___x_3192_, 5, v_synthPendingDepth_3186_);
lean_ctor_set(v___x_3192_, 6, v_customCanUnfoldPredicate_x3f_3187_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7, v_trackZetaDelta_3181_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 1, v_univApprox_3188_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3189_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 3, v_cacheInferType_3190_);
lean_inc(v_a_3134_);
lean_inc_ref(v_a_3133_);
lean_inc(v_a_3132_);
v___x_3193_ = lean_whnf(v_type_3130_, v___x_3192_, v_a_3132_, v_a_3133_, v_a_3134_);
v___y_3137_ = v___x_3193_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3194_; 
lean_inc(v_a_3134_);
lean_inc_ref(v_a_3133_);
lean_inc(v_a_3132_);
lean_inc_ref(v_a_3131_);
v___x_3194_ = lean_whnf(v_type_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
v___y_3137_ = v___x_3194_;
goto v___jp_3136_;
}
v___jp_3136_:
{
if (lean_obj_tag(v___y_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3167_; 
v_a_3138_ = lean_ctor_get(v___y_3137_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___y_3137_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3140_ = v___y_3137_;
v_isShared_3141_ = v_isSharedCheck_3167_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___y_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3167_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
if (lean_obj_tag(v_a_3138_) == 5)
{
lean_object* v_fn_3142_; lean_object* v_arg_3143_; lean_object* v___x_3144_; lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3162_; 
lean_del_object(v___x_3140_);
v_fn_3142_ = lean_ctor_get(v_a_3138_, 0);
lean_inc_ref(v_fn_3142_);
v_arg_3143_ = lean_ctor_get(v_a_3138_, 1);
lean_inc_ref(v_arg_3143_);
lean_dec_ref_known(v_a_3138_, 2);
v___x_3144_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3142_, v_a_3132_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3162_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3162_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3161_; 
v___x_3149_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3143_, v_a_3132_);
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3161_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3161_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_a_3145_);
lean_ctor_set(v___x_3154_, 1, v_a_3150_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 1);
lean_ctor_set(v___x_3147_, 0, v___x_3154_);
v___x_3156_ = v___x_3147_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3156_);
v___x_3158_ = v___x_3152_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_dec(v_a_3138_);
v___x_3163_ = lean_box(0);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3163_);
v___x_3165_ = v___x_3140_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_a_3168_ = lean_ctor_get(v___y_3137_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___y_3137_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___y_3137_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___y_3137_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Meta_isTypeApp_x3f(v_type_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Meta_isTypeApp_x3f(v_type_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3244_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3244_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3244_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
if (lean_obj_tag(v_a_3209_) == 1)
{
lean_object* v_val_3213_; lean_object* v_fst_3214_; lean_object* v___x_3215_; 
lean_del_object(v___x_3211_);
v_val_3213_ = lean_ctor_get(v_a_3209_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v_a_3209_, 1);
v_fst_3214_ = lean_ctor_get(v_val_3213_, 0);
lean_inc(v_fst_3214_);
lean_dec(v_val_3213_);
v___x_3215_ = l_Lean_Meta_isMonad_x3f(v_fst_3214_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3230_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3218_ = v___x_3215_;
v_isShared_3219_ = v_isSharedCheck_3230_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3215_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3230_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
if (lean_obj_tag(v_a_3216_) == 0)
{
uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3220_ = 0;
v___x_3221_ = lean_box(v___x_3220_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3221_);
v___x_3223_ = v___x_3218_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
else
{
uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
lean_dec_ref_known(v_a_3216_, 1);
v___x_3225_ = 1;
v___x_3226_ = lean_box(v___x_3225_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3226_);
v___x_3228_ = v___x_3218_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v_a_3231_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3215_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3215_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_dec(v_a_3209_);
v___x_3239_ = 0;
v___x_3240_ = lean_box(v___x_3239_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3240_);
v___x_3242_ = v___x_3211_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_a_3245_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3208_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3208_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_Meta_isMonadApp(v_type_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
return v_res_3259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3260_, lean_object* v_opt_3261_){
_start:
{
lean_object* v_name_3262_; lean_object* v_defValue_3263_; lean_object* v_map_3264_; lean_object* v___x_3265_; 
v_name_3262_ = lean_ctor_get(v_opt_3261_, 0);
v_defValue_3263_ = lean_ctor_get(v_opt_3261_, 1);
v_map_3264_ = lean_ctor_get(v_opts_3260_, 0);
v___x_3265_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3264_, v_name_3262_);
if (lean_obj_tag(v___x_3265_) == 0)
{
uint8_t v___x_3266_; 
v___x_3266_ = lean_unbox(v_defValue_3263_);
return v___x_3266_;
}
else
{
lean_object* v_val_3267_; 
v_val_3267_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3265_, 1);
if (lean_obj_tag(v_val_3267_) == 1)
{
uint8_t v_v_3268_; 
v_v_3268_ = lean_ctor_get_uint8(v_val_3267_, 0);
lean_dec_ref_known(v_val_3267_, 0);
return v_v_3268_;
}
else
{
uint8_t v___x_3269_; 
lean_dec(v_val_3267_);
v___x_3269_ = lean_unbox(v_defValue_3263_);
return v___x_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3270_, lean_object* v_opt_3271_){
_start:
{
uint8_t v_res_3272_; lean_object* v_r_3273_; 
v_res_3272_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3270_, v_opt_3271_);
lean_dec_ref(v_opt_3271_);
lean_dec_ref(v_opts_3270_);
v_r_3273_ = lean_box(v_res_3272_);
return v_r_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec_ref(v_x_3284_);
return v_res_3290_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = l_Lean_mkBVar(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3313_, lean_object* v_expectedType_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v_a_3327_; lean_object* v___y_3331_; lean_object* v___x_3341_; lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3746_; 
v___x_3341_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3314_, v_a_3316_);
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3746_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3746_;
goto v_resetjp_3343_;
}
v___jp_3320_:
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec_ref(v___y_3321_);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___y_3321_);
return v___x_3325_;
}
}
v___jp_3326_:
{
uint8_t v___x_3328_; 
v___x_3328_ = l_Lean_Exception_isInterrupt(v_a_3327_);
if (v___x_3328_ == 0)
{
uint8_t v___x_3329_; 
lean_inc_ref(v_a_3327_);
v___x_3329_ = l_Lean_Exception_isRuntime(v_a_3327_);
v___y_3321_ = v_a_3327_;
v___y_3322_ = v___x_3329_;
goto v___jp_3320_;
}
else
{
v___y_3321_ = v_a_3327_;
v___y_3322_ = v___x_3328_;
goto v___jp_3320_;
}
}
v___jp_3330_:
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3340_; 
v_a_3332_ = lean_ctor_get(v___y_3331_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___y_3331_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3334_ = v___y_3331_;
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___y_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3340_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v_a_3336_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v_a_3332_, 0);
lean_inc(v_a_3336_);
lean_dec(v_a_3332_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v_a_3336_);
v___x_3338_ = v___x_3334_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; 
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc_ref(v_e_3313_);
v___x_3346_ = lean_infer_type(v_e_3313_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3737_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3347_, v_a_3316_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3737_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3737_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; 
lean_inc(v_a_3342_);
v___x_3353_ = l_Lean_Meta_isTypeApp_x3f(v_a_3342_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3728_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3728_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3728_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
if (lean_obj_tag(v_a_3354_) == 1)
{
lean_object* v_val_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3723_; 
lean_del_object(v___x_3356_);
v_val_3358_ = lean_ctor_get(v_a_3354_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_a_3354_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3360_ = v_a_3354_;
v_isShared_3361_ = v_isSharedCheck_3723_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_val_3358_);
lean_dec(v_a_3354_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3723_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3722_; 
v_fst_3362_ = lean_ctor_get(v_val_3358_, 0);
v_snd_3363_ = lean_ctor_get(v_val_3358_, 1);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_val_3358_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3365_ = v_val_3358_;
v_isShared_3366_ = v_isSharedCheck_3722_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3362_);
lean_dec(v_val_3358_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3722_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; 
lean_inc(v_a_3349_);
v___x_3367_ = l_Lean_Meta_isTypeApp_x3f(v_a_3349_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3713_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3713_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3713_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
if (lean_obj_tag(v_a_3368_) == 1)
{
lean_object* v_val_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3708_; 
lean_del_object(v___x_3370_);
v_val_3372_ = lean_ctor_get(v_a_3368_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3374_ = v_a_3368_;
v_isShared_3375_ = v_isSharedCheck_3708_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_val_3372_);
lean_dec(v_a_3368_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3708_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3707_; 
v_fst_3376_ = lean_ctor_get(v_val_3372_, 0);
v_snd_3377_ = lean_ctor_get(v_val_3372_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_val_3372_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3379_ = v_val_3372_;
v_isShared_3380_ = v_isSharedCheck_3707_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_inc(v_fst_3376_);
lean_dec(v_val_3372_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3707_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_saveState___redArg(v_a_3316_, v_a_3318_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
lean_inc(v_fst_3362_);
lean_inc(v_fst_3376_);
v___x_3383_ = l_Lean_Meta_isExprDefEq(v_fst_3376_, v_fst_3362_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3690_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3690_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3690_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
uint8_t v___x_3388_; 
v___x_3388_ = lean_unbox(v_a_3384_);
lean_dec(v_a_3384_);
if (v___x_3388_ == 0)
{
lean_object* v_toCold_3389_; lean_object* v_options_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
lean_dec(v_a_3382_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3344_);
v_toCold_3389_ = lean_ctor_get(v_a_3317_, 0);
v_options_3390_ = lean_ctor_get(v_toCold_3389_, 2);
v___x_3391_ = l_Lean_Meta_autoLift;
v___x_3392_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3393_ = lean_box(0);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3393_);
v___x_3395_ = v___x_3386_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
else
{
lean_object* v___x_3397_; 
lean_del_object(v___x_3386_);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc(v_fst_3376_);
v___x_3397_ = lean_infer_type(v_fst_3376_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
v___x_3399_ = lean_whnf(v_a_3398_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
if (lean_obj_tag(v_a_3400_) == 7)
{
lean_object* v_binderType_3401_; 
v_binderType_3401_ = lean_ctor_get(v_a_3400_, 1);
if (lean_obj_tag(v_binderType_3401_) == 3)
{
lean_object* v_body_3402_; 
v_body_3402_ = lean_ctor_get(v_a_3400_, 2);
if (lean_obj_tag(v_body_3402_) == 3)
{
lean_object* v_u_3403_; lean_object* v_u_3404_; lean_object* v___x_3405_; 
lean_inc_ref(v_body_3402_);
lean_inc_ref(v_binderType_3401_);
lean_dec_ref_known(v_a_3400_, 3);
v_u_3403_ = lean_ctor_get(v_binderType_3401_, 0);
lean_inc(v_u_3403_);
lean_dec_ref_known(v_binderType_3401_, 1);
v_u_3404_ = lean_ctor_get(v_body_3402_, 0);
lean_inc(v_u_3404_);
lean_dec_ref_known(v_body_3402_, 1);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc(v_fst_3362_);
v___x_3405_ = lean_infer_type(v_fst_3362_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
v___x_3407_ = lean_whnf(v_a_3406_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 7)
{
lean_object* v_binderType_3409_; 
v_binderType_3409_ = lean_ctor_get(v_a_3408_, 1);
if (lean_obj_tag(v_binderType_3409_) == 3)
{
lean_object* v_body_3410_; 
v_body_3410_ = lean_ctor_get(v_a_3408_, 2);
if (lean_obj_tag(v_body_3410_) == 3)
{
lean_object* v_u_3411_; lean_object* v_u_3412_; lean_object* v___x_3413_; 
lean_inc_ref(v_body_3410_);
lean_inc_ref(v_binderType_3409_);
lean_dec_ref_known(v_a_3408_, 3);
v_u_3411_ = lean_ctor_get(v_binderType_3409_, 0);
lean_inc(v_u_3411_);
lean_dec_ref_known(v_binderType_3409_, 1);
v_u_3412_ = lean_ctor_get(v_body_3410_, 0);
lean_inc(v_u_3412_);
lean_dec_ref_known(v_body_3410_, 1);
v___x_3413_ = l_Lean_Meta_decLevel(v_u_3403_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = l_Lean_Meta_decLevel(v_u_3411_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
lean_inc(v_a_3414_);
v___x_3417_ = l_Lean_Meta_isLevelDefEq(v_a_3414_, v_a_3416_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3582_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3582_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3582_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_unbox(v_a_3418_);
lean_dec(v_a_3418_);
if (v___x_3422_ == 1)
{
lean_object* v___x_3423_; 
lean_del_object(v___x_3420_);
v___x_3423_ = l_Lean_Meta_decLevel(v_u_3404_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = l_Lean_Meta_decLevel(v_u_3412_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3428_ = lean_box(0);
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 1);
lean_ctor_set(v___x_3379_, 1, v___x_3428_);
lean_ctor_set(v___x_3379_, 0, v_a_3426_);
v___x_3430_ = v___x_3379_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3432_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 1);
lean_ctor_set(v___x_3365_, 1, v___x_3430_);
lean_ctor_set(v___x_3365_, 0, v_a_3424_);
v___x_3432_ = v___x_3365_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3424_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_a_3414_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_Expr_const___override(v___x_3427_, v___x_3433_);
v___x_3435_ = lean_unsigned_to_nat(2u);
v___x_3436_ = lean_mk_empty_array_with_capacity(v___x_3435_);
lean_inc(v_fst_3376_);
v___x_3437_ = lean_array_push(v___x_3436_, v_fst_3376_);
lean_inc(v_fst_3362_);
v___x_3438_ = lean_array_push(v___x_3437_, v_fst_3362_);
v___x_3439_ = l_Lean_mkAppN(v___x_3434_, v___x_3438_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_Meta_trySynthInstance(v___x_3439_, v___x_3440_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3572_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3572_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3572_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
if (lean_obj_tag(v_a_3442_) == 1)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
lean_del_object(v___x_3444_);
v_a_3446_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v_a_3442_, 1);
lean_inc(v_snd_3377_);
v___x_3447_ = l_Lean_Meta_getDecLevel(v_snd_3377_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
v___x_3449_ = l_Lean_Meta_getDecLevel(v_a_3349_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3451_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
lean_inc(v_a_3342_);
v___x_3451_ = l_Lean_Meta_getDecLevel(v_a_3342_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3454_, 0, v_a_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3428_);
v___x_3455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_a_3450_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_a_3448_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
lean_inc_ref(v___x_3456_);
v___x_3457_ = l_Lean_mkConst(v___x_3453_, v___x_3456_);
v___x_3458_ = lean_unsigned_to_nat(5u);
v___x_3459_ = lean_mk_empty_array_with_capacity(v___x_3458_);
lean_inc(v_fst_3376_);
v___x_3460_ = lean_array_push(v___x_3459_, v_fst_3376_);
lean_inc(v_fst_3362_);
v___x_3461_ = lean_array_push(v___x_3460_, v_fst_3362_);
lean_inc(v_a_3446_);
v___x_3462_ = lean_array_push(v___x_3461_, v_a_3446_);
lean_inc(v_snd_3377_);
v___x_3463_ = lean_array_push(v___x_3462_, v_snd_3377_);
lean_inc_ref(v_e_3313_);
v___x_3464_ = lean_array_push(v___x_3463_, v_e_3313_);
v___x_3465_ = l_Lean_mkAppN(v___x_3457_, v___x_3464_);
lean_dec_ref(v___x_3464_);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc_ref(v___x_3465_);
v___x_3466_ = lean_infer_type(v___x_3465_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3468_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
lean_inc(v_a_3342_);
v___x_3468_ = l_Lean_Meta_isExprDefEq(v_a_3342_, v_a_3467_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3563_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3563_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3563_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
uint8_t v___x_3473_; 
v___x_3473_ = lean_unbox(v_a_3469_);
lean_dec(v_a_3469_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_del_object(v___x_3471_);
lean_dec_ref(v___x_3465_);
lean_del_object(v___x_3374_);
lean_inc(v_fst_3362_);
v___x_3474_ = l_Lean_Meta_isMonad_x3f(v_fst_3362_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3555_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3555_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3555_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
if (lean_obj_tag(v_a_3475_) == 1)
{
lean_object* v_val_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3551_; 
lean_del_object(v___x_3477_);
v_val_3479_ = lean_ctor_get(v_a_3475_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_a_3475_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3481_ = v_a_3475_;
v_isShared_3482_ = v_isSharedCheck_3551_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_val_3479_);
lean_dec(v_a_3475_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3551_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; 
lean_inc(v_snd_3377_);
v___x_3483_ = l_Lean_Meta_getLevel(v_snd_3377_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
lean_inc(v_snd_3363_);
v___x_3485_ = l_Lean_Meta_getLevel(v_snd_3363_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3488_ = 0;
v___x_3489_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3490_, 0, v_a_3486_);
lean_ctor_set(v___x_3490_, 1, v___x_3428_);
v___x_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3491_, 0, v_a_3484_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_mkConst(v___x_3489_, v___x_3491_);
v___x_3493_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3494_ = lean_unsigned_to_nat(3u);
v___x_3495_ = lean_mk_empty_array_with_capacity(v___x_3494_);
lean_inc_n(v_snd_3377_, 2);
v___x_3496_ = lean_array_push(v___x_3495_, v_snd_3377_);
v___x_3497_ = lean_array_push(v___x_3496_, v___x_3493_);
lean_inc(v_snd_3363_);
v___x_3498_ = lean_array_push(v___x_3497_, v_snd_3363_);
v___x_3499_ = l_Lean_mkAppN(v___x_3492_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3500_ = l_Lean_mkForall(v___x_3487_, v___x_3488_, v_snd_3377_, v___x_3499_);
v___x_3501_ = l_Lean_Meta_trySynthInstance(v___x_3500_, v___x_3440_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3547_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3547_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3547_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
if (lean_obj_tag(v_a_3502_) == 1)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_del_object(v___x_3504_);
v_a_3506_ = lean_ctor_get(v_a_3502_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v_a_3502_, 1);
v___x_3507_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3508_ = l_Lean_mkConst(v___x_3507_, v___x_3456_);
v___x_3509_ = lean_unsigned_to_nat(8u);
v___x_3510_ = lean_mk_empty_array_with_capacity(v___x_3509_);
v___x_3511_ = lean_array_push(v___x_3510_, v_fst_3376_);
v___x_3512_ = lean_array_push(v___x_3511_, v_fst_3362_);
v___x_3513_ = lean_array_push(v___x_3512_, v_snd_3377_);
v___x_3514_ = lean_array_push(v___x_3513_, v_snd_3363_);
v___x_3515_ = lean_array_push(v___x_3514_, v_a_3446_);
v___x_3516_ = lean_array_push(v___x_3515_, v_a_3506_);
v___x_3517_ = lean_array_push(v___x_3516_, v_val_3479_);
v___x_3518_ = lean_array_push(v___x_3517_, v_e_3313_);
v___x_3519_ = l_Lean_mkAppN(v___x_3508_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = l_Lean_Meta_expandCoe(v___x_3519_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_fst_3522_; lean_object* v___x_3523_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
lean_inc_n(v_fst_3522_, 2);
lean_dec(v_a_3521_);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
v___x_3523_ = lean_infer_type(v_fst_3522_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = l_Lean_Meta_isExprDefEq(v_a_3342_, v_a_3524_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3540_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3540_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3540_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
uint8_t v___x_3530_; 
v___x_3530_ = lean_unbox(v_a_3526_);
lean_dec(v_a_3526_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3532_; 
lean_dec(v_fst_3522_);
lean_del_object(v___x_3481_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3440_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3440_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
else
{
lean_object* v___x_3535_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v_fst_3522_);
v___x_3535_ = v___x_3481_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_fst_3522_);
v___x_3535_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3537_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3535_);
v___x_3537_ = v___x_3528_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; 
lean_dec(v_fst_3522_);
lean_del_object(v___x_3481_);
v_a_3541_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3525_, 1);
v_a_3327_ = v_a_3541_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3542_; 
lean_dec(v_fst_3522_);
lean_del_object(v___x_3481_);
lean_dec(v_a_3342_);
v_a_3542_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3523_, 1);
v_a_3327_ = v_a_3542_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3543_; 
lean_del_object(v___x_3481_);
lean_dec(v_a_3342_);
v_a_3543_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3520_, 1);
v_a_3327_ = v_a_3543_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3545_; 
lean_dec(v_a_3502_);
lean_del_object(v___x_3481_);
lean_dec(v_val_3479_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3440_);
v___x_3545_ = v___x_3504_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3440_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; 
lean_del_object(v___x_3481_);
lean_dec(v_val_3479_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3548_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3501_, 1);
v_a_3327_ = v_a_3548_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3549_; 
lean_dec(v_a_3484_);
lean_del_object(v___x_3481_);
lean_dec(v_val_3479_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3549_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3485_, 1);
v_a_3327_ = v_a_3549_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3550_; 
lean_del_object(v___x_3481_);
lean_dec(v_val_3479_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3550_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3483_, 1);
v_a_3327_ = v_a_3550_;
goto v___jp_3326_;
}
}
}
else
{
lean_object* v___x_3553_; 
lean_dec(v_a_3475_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3440_);
v___x_3553_ = v___x_3477_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3440_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; 
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3556_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3474_, 1);
v_a_3327_ = v_a_3556_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3558_; 
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3465_);
v___x_3558_ = v___x_3374_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3465_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3560_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3558_);
v___x_3560_ = v___x_3471_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
else
{
lean_object* v_a_3564_; 
lean_dec_ref(v___x_3465_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3564_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3468_, 1);
v_a_3327_ = v_a_3564_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3565_; 
lean_dec_ref(v___x_3465_);
lean_dec_ref_known(v___x_3456_, 2);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3565_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3466_, 1);
v_a_3327_ = v_a_3565_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3566_; 
lean_dec(v_a_3450_);
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3566_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3451_, 1);
v_a_3327_ = v_a_3566_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3567_; 
lean_dec(v_a_3448_);
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3567_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3449_, 1);
v_a_3327_ = v_a_3567_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3568_; 
lean_dec(v_a_3446_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3568_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3447_, 1);
v_a_3327_ = v_a_3568_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3570_; 
lean_dec(v_a_3442_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3440_);
v___x_3570_ = v___x_3444_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3440_);
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
lean_object* v_a_3573_; 
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3573_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3441_, 1);
v_a_3327_ = v_a_3573_;
goto v___jp_3326_;
}
}
}
}
else
{
lean_object* v_a_3576_; 
lean_dec(v_a_3424_);
lean_dec(v_a_3414_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3576_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3425_, 1);
v_a_3327_ = v_a_3576_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3577_; 
lean_dec(v_a_3414_);
lean_dec(v_u_3412_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3577_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3423_, 1);
v_a_3327_ = v_a_3577_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_dec(v_a_3414_);
lean_dec(v_u_3412_);
lean_dec(v_u_3404_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3578_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3578_);
v___x_3580_ = v___x_3420_;
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
lean_object* v_a_3583_; 
lean_dec(v_a_3414_);
lean_dec(v_u_3412_);
lean_dec(v_u_3404_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3583_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3417_, 1);
v_a_3327_ = v_a_3583_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3584_; 
lean_dec(v_a_3414_);
lean_dec(v_u_3412_);
lean_dec(v_u_3404_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3584_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3415_, 1);
v_a_3327_ = v_a_3584_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3585_; 
lean_dec(v_u_3412_);
lean_dec(v_u_3411_);
lean_dec(v_u_3404_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3585_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3413_, 1);
v_a_3327_ = v_a_3585_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3586_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3586_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3408_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec_ref_known(v_a_3408_, 3);
v___y_3331_ = v___x_3586_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3587_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3587_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3408_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec_ref_known(v_a_3408_, 3);
v___y_3331_ = v___x_3587_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3588_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3588_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3408_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec(v_a_3408_);
v___y_3331_ = v___x_3588_;
goto v___jp_3330_;
}
}
else
{
lean_object* v_a_3589_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3589_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3407_, 1);
v_a_3327_ = v_a_3589_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3590_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3590_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3405_, 1);
v_a_3327_ = v_a_3590_;
goto v___jp_3326_;
}
}
else
{
lean_object* v___x_3591_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3591_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec_ref_known(v_a_3400_, 3);
v___y_3331_ = v___x_3591_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3592_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3592_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec_ref_known(v_a_3400_, 3);
v___y_3331_ = v___x_3592_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3593_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3593_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec(v_a_3400_);
v___y_3331_ = v___x_3593_;
goto v___jp_3330_;
}
}
else
{
lean_object* v_a_3594_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3594_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3399_, 1);
v_a_3327_ = v_a_3594_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3595_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3595_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3397_, 1);
v_a_3327_ = v_a_3595_;
goto v___jp_3326_;
}
}
}
else
{
lean_object* v___x_3596_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3365_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
v___x_3596_ = l_Lean_Meta_isMonad_x3f(v_fst_3362_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3689_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3689_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3689_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
if (lean_obj_tag(v_a_3597_) == 1)
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v_fst_3376_);
v___x_3603_ = v___x_3374_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_fst_3376_);
v___x_3603_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v_snd_3377_);
v___x_3605_ = v___x_3360_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_snd_3377_);
v___x_3605_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 1);
lean_ctor_set(v___x_3351_, 0, v_snd_3363_);
v___x_3607_ = v___x_3351_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_snd_3363_);
v___x_3607_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___y_3610_; uint8_t v___y_3611_; lean_object* v_a_3633_; lean_object* v___x_3637_; 
v___x_3608_ = lean_box(0);
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 1);
lean_ctor_set(v___x_3344_, 0, v_e_3313_);
v___x_3637_ = v___x_3344_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_e_3313_);
v___x_3637_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3636_;
}
v___jp_3609_:
{
if (v___y_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_dec_ref(v___y_3610_);
lean_del_object(v___x_3599_);
v___x_3612_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3382_, v_a_3316_, v_a_3318_);
lean_dec(v_a_3382_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v___x_3612_, 0);
lean_dec(v_unused_3620_);
v___x_3614_ = v___x_3612_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v___x_3612_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3608_);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3608_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3612_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3612_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
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
else
{
lean_object* v___x_3630_; 
lean_dec(v_a_3382_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
lean_ctor_set(v___x_3599_, 0, v___y_3610_);
v___x_3630_ = v___x_3599_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___y_3610_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
v___jp_3632_:
{
uint8_t v___x_3634_; 
v___x_3634_ = l_Lean_Exception_isInterrupt(v_a_3633_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
lean_inc_ref(v_a_3633_);
v___x_3635_ = l_Lean_Exception_isRuntime(v_a_3633_);
v___y_3610_ = v_a_3633_;
v___y_3611_ = v___x_3635_;
goto v___jp_3609_;
}
else
{
v___y_3610_ = v_a_3633_;
v___y_3611_ = v___x_3634_;
goto v___jp_3609_;
}
}
v_reusejp_3636_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3638_ = lean_unsigned_to_nat(6u);
v___x_3639_ = lean_mk_empty_array_with_capacity(v___x_3638_);
v___x_3640_ = lean_array_push(v___x_3639_, v___x_3603_);
v___x_3641_ = lean_array_push(v___x_3640_, v___x_3605_);
v___x_3642_ = lean_array_push(v___x_3641_, v___x_3607_);
v___x_3643_ = lean_array_push(v___x_3642_, v___x_3608_);
v___x_3644_ = lean_array_push(v___x_3643_, v_a_3597_);
v___x_3645_ = lean_array_push(v___x_3644_, v___x_3637_);
v___x_3646_ = l_Lean_Meta_mkAppOptM(v___x_3601_, v___x_3645_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3665_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3665_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3665_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_Meta_expandCoe(v_a_3647_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3599_);
lean_dec(v_a_3382_);
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3663_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_fst_3656_; lean_object* v___x_3658_; 
v_fst_3656_ = lean_ctor_get(v_a_3652_, 0);
lean_inc(v_fst_3656_);
lean_dec(v_a_3652_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 1);
lean_ctor_set(v___x_3649_, 0, v_fst_3656_);
v___x_3658_ = v___x_3649_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_fst_3656_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3658_);
v___x_3660_ = v___x_3654_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
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
lean_object* v_a_3664_; 
lean_del_object(v___x_3649_);
v_a_3664_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3651_, 1);
v_a_3633_ = v_a_3664_;
goto v___jp_3632_;
}
}
}
else
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3646_, 1);
v_a_3633_ = v_a_3666_;
goto v___jp_3632_;
}
}
}
}
}
}
else
{
lean_object* v___x_3671_; 
lean_del_object(v___x_3599_);
lean_dec(v_a_3597_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3344_);
lean_dec_ref(v_e_3313_);
v___x_3671_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3382_, v_a_3316_, v_a_3318_);
lean_dec(v_a_3382_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3679_; 
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v___x_3671_, 0);
lean_dec(v_unused_3680_);
v___x_3673_ = v___x_3671_;
v_isShared_3674_ = v_isSharedCheck_3679_;
goto v_resetjp_3672_;
}
else
{
lean_dec(v___x_3671_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3679_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = lean_box(0);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3675_);
v___x_3677_ = v___x_3673_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
v_a_3681_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3671_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3671_);
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
}
else
{
lean_dec(v_a_3382_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3363_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_del_object(v___x_3344_);
lean_dec_ref(v_e_3313_);
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_a_3382_);
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3691_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3383_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3383_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_del_object(v___x_3379_);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3699_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3381_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3381_);
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
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3711_; 
lean_dec(v_a_3368_);
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3709_ = lean_box(0);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3709_);
v___x_3711_ = v___x_3370_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_del_object(v___x_3365_);
lean_dec(v_snd_3363_);
lean_dec(v_fst_3362_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3714_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3367_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3367_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3726_; 
lean_dec(v_a_3354_);
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v___x_3724_ = lean_box(0);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3724_);
v___x_3726_ = v___x_3356_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_del_object(v___x_3351_);
lean_dec(v_a_3349_);
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3729_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3353_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3353_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
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
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_del_object(v___x_3344_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3313_);
v_a_3738_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3346_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3346_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3747_, lean_object* v_expectedType_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3747_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3755_, lean_object* v_expectedType_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_){
_start:
{
lean_object* v___x_3762_; 
lean_inc_ref(v_expectedType_3756_);
lean_inc_ref(v_expr_3755_);
v___x_3762_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3755_, v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3842_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3842_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3842_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
if (lean_obj_tag(v_a_3763_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_val_3767_ = lean_ctor_get(v_a_3763_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3763_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3769_ = v_a_3763_;
v_isShared_3770_ = v_isSharedCheck_3779_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_val_3767_);
lean_dec(v_a_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3779_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v_val_3767_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3772_);
v___x_3774_ = v___x_3769_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3774_);
v___x_3776_ = v___x_3765_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
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
else
{
lean_object* v___x_3780_; 
lean_del_object(v___x_3765_);
lean_dec(v_a_3763_);
lean_inc_ref(v_expectedType_3756_);
v___x_3780_ = l_Lean_Meta_whnfR(v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; uint8_t v___x_3782_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l_Lean_Expr_isForall(v_a_3781_);
lean_dec(v_a_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3755_, v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
return v___x_3783_;
}
else
{
lean_object* v___x_3784_; 
lean_inc_ref(v_expr_3755_);
v___x_3784_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3755_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
if (lean_obj_tag(v_a_3785_) == 1)
{
lean_object* v_val_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3824_; 
v_val_3786_ = lean_ctor_get(v_a_3785_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3785_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3788_ = v_a_3785_;
v_isShared_3789_ = v_isSharedCheck_3824_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_val_3786_);
lean_dec(v_a_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3824_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; 
lean_inc(v_a_3760_);
lean_inc_ref(v_a_3759_);
lean_inc(v_a_3758_);
lean_inc_ref(v_a_3757_);
lean_inc(v_val_3786_);
v___x_3790_ = lean_infer_type(v_val_3786_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
lean_inc_ref(v_expectedType_3756_);
v___x_3792_ = l_Lean_Meta_isExprDefEq(v_a_3791_, v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3807_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_unbox(v_a_3793_);
lean_dec(v_a_3793_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; 
lean_del_object(v___x_3795_);
lean_del_object(v___x_3788_);
lean_dec(v_val_3786_);
v___x_3798_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3755_, v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v___x_3799_ = lean_box(0);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v_val_3786_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3800_);
v___x_3802_ = v___x_3788_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3804_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3802_);
v___x_3804_ = v___x_3795_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_del_object(v___x_3788_);
lean_dec(v_val_3786_);
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_a_3808_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3792_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3792_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_del_object(v___x_3788_);
lean_dec(v_val_3786_);
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_a_3816_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3790_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3790_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
lean_object* v___x_3825_; 
lean_dec(v_a_3785_);
v___x_3825_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3755_, v_expectedType_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
return v___x_3825_;
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_a_3826_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3784_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3784_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_a_3834_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3780_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3780_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v_expectedType_3756_);
lean_dec_ref(v_expr_3755_);
v_a_3843_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3762_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3762_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3851_, lean_object* v_expectedType_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3851_, v_expectedType_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_a_3854_);
lean_dec_ref(v_a_3853_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3859_, lean_object* v_expectedType_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3859_, v_expectedType_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3891_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3891_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3891_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
switch(lean_obj_tag(v_a_3867_))
{
case 0:
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = lean_box(0);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3871_);
v___x_3873_ = v___x_3869_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
case 1:
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3886_; 
v_a_3875_ = lean_ctor_get(v_a_3867_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_a_3867_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3877_ = v_a_3867_;
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v_a_3867_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3886_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_fst_3879_; lean_object* v___x_3881_; 
v_fst_3879_ = lean_ctor_get(v_a_3875_, 0);
lean_inc(v_fst_3879_);
lean_dec(v_a_3875_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_fst_3879_);
v___x_3881_ = v___x_3877_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_fst_3879_);
v___x_3881_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3883_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3881_);
v___x_3883_ = v___x_3869_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3881_);
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
default: 
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = lean_box(2);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3887_);
v___x_3889_ = v___x_3869_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_a_3892_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3866_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3866_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3900_, lean_object* v_expectedType_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Meta_coerce_x3f(v_expr_3900_, v_expectedType_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
return v_res_3907_;
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
