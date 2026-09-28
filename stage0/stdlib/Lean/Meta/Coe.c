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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
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
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 307, .m_capacity = 307, .m_length = 306, .m_data = "Tags declarations to be unfolded during coercion elaboration.\n\nThis is mostly used to hide coercion implementation details and show the coerced result instead of\nan application of auxiliary definitions (e.g. `CoeT.coe`, `Coe.coe`). This attribute only works on\nreducible functions and instance projections."};
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_256_; 
v_ref_208_ = lean_ctor_get(v___y_205_, 2);
v___x_209_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_201_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_256_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_256_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_256_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_traceState_215_; lean_object* v_env_216_; lean_object* v_nextMacroScope_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_cache_220_; lean_object* v_recordedDeps_221_; lean_object* v_messages_222_; lean_object* v_infoState_223_; lean_object* v_snapshotTasks_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_255_; 
v___x_214_ = lean_st_ref_take(v___y_206_);
v_traceState_215_ = lean_ctor_get(v___x_214_, 4);
v_env_216_ = lean_ctor_get(v___x_214_, 0);
v_nextMacroScope_217_ = lean_ctor_get(v___x_214_, 1);
v_ngen_218_ = lean_ctor_get(v___x_214_, 2);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_214_, 3);
v_cache_220_ = lean_ctor_get(v___x_214_, 5);
v_recordedDeps_221_ = lean_ctor_get(v___x_214_, 6);
v_messages_222_ = lean_ctor_get(v___x_214_, 7);
v_infoState_223_ = lean_ctor_get(v___x_214_, 8);
v_snapshotTasks_224_ = lean_ctor_get(v___x_214_, 9);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_255_ == 0)
{
v___x_226_ = v___x_214_;
v_isShared_227_ = v_isSharedCheck_255_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_snapshotTasks_224_);
lean_inc(v_infoState_223_);
lean_inc(v_messages_222_);
lean_inc(v_recordedDeps_221_);
lean_inc(v_cache_220_);
lean_inc(v_traceState_215_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_env_216_);
lean_dec(v___x_214_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_255_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
uint64_t v_tid_228_; lean_object* v_traces_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_254_; 
v_tid_228_ = lean_ctor_get_uint64(v_traceState_215_, sizeof(void*)*1);
v_traces_229_ = lean_ctor_get(v_traceState_215_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_traceState_215_);
if (v_isSharedCheck_254_ == 0)
{
v___x_231_ = v_traceState_215_;
v_isShared_232_ = v_isSharedCheck_254_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_traces_229_);
lean_dec(v_traceState_215_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_254_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; double v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_box(0);
v___x_235_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_236_ = 0;
v___x_237_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_238_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_238_, 0, v_cls_200_);
lean_ctor_set(v___x_238_, 1, v___x_234_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_ctor_set_float(v___x_238_, sizeof(void*)*3, v___x_235_);
lean_ctor_set_float(v___x_238_, sizeof(void*)*3 + 8, v___x_235_);
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*3 + 16, v___x_236_);
v___x_239_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_240_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v_a_210_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_inc(v_ref_208_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_ref_208_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_PersistentArray_push___redArg(v_traces_229_, v___x_241_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_242_);
v___x_244_ = v___x_231_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_242_);
lean_ctor_set_uint64(v_reuseFailAlloc_253_, sizeof(void*)*1, v_tid_228_);
v___x_244_ = v_reuseFailAlloc_253_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 4, v___x_244_);
v___x_246_ = v___x_226_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_env_216_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_recordedDeps_221_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_messages_222_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_infoState_223_);
lean_ctor_set(v_reuseFailAlloc_252_, 9, v_snapshotTasks_224_);
v___x_246_ = v_reuseFailAlloc_252_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_st_ref_put(v___y_206_, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_233_);
lean_ctor_set(v___x_248_, 1, v___y_202_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_248_);
v___x_250_ = v___x_212_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_257_, v_msg_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_266_, lean_object* v_i_267_, lean_object* v_k_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_get_size(v_keys_266_);
v___x_270_ = lean_nat_dec_lt(v_i_267_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v_i_267_);
return v___x_270_;
}
else
{
lean_object* v_k_x27_271_; uint8_t v___x_272_; 
v_k_x27_271_ = lean_array_fget_borrowed(v_keys_266_, v_i_267_);
v___x_272_ = l_Lean_instBEqExtraModUse_beq(v_k_268_, v_k_x27_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_i_267_, v___x_273_);
lean_dec(v_i_267_);
v_i_267_ = v___x_274_;
goto _start;
}
else
{
lean_dec(v_i_267_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_276_, lean_object* v_i_277_, lean_object* v_k_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_276_, v_i_277_, v_k_278_);
lean_dec_ref(v_k_278_);
lean_dec_ref(v_keys_276_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_281_, size_t v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_es_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v_j_288_; lean_object* v___x_289_; 
v_es_284_ = lean_ctor_get(v_x_281_, 0);
v___x_285_ = lean_box(2);
v___x_286_ = ((size_t)31ULL);
v___x_287_ = lean_usize_land(v_x_282_, v___x_286_);
v_j_288_ = lean_usize_to_nat(v___x_287_);
v___x_289_ = lean_array_get_borrowed(v___x_285_, v_es_284_, v_j_288_);
lean_dec(v_j_288_);
switch(lean_obj_tag(v___x_289_))
{
case 0:
{
lean_object* v_key_290_; uint8_t v___x_291_; 
v_key_290_ = lean_ctor_get(v___x_289_, 0);
v___x_291_ = l_Lean_instBEqExtraModUse_beq(v_x_283_, v_key_290_);
return v___x_291_;
}
case 1:
{
lean_object* v_node_292_; size_t v___x_293_; size_t v___x_294_; 
v_node_292_ = lean_ctor_get(v___x_289_, 0);
v___x_293_ = ((size_t)5ULL);
v___x_294_ = lean_usize_shift_right(v_x_282_, v___x_293_);
v_x_281_ = v_node_292_;
v_x_282_ = v___x_294_;
goto _start;
}
default: 
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
}
}
else
{
lean_object* v_ks_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_ks_297_ = lean_ctor_get(v_x_281_, 0);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_297_, v___x_298_, v_x_283_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
size_t v_x_36170__boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_x_36170__boxed_303_ = lean_unbox_usize(v_x_301_);
lean_dec(v_x_301_);
v_res_304_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_300_, v_x_36170__boxed_303_, v_x_302_);
lean_dec_ref(v_x_302_);
lean_dec_ref(v_x_300_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint64_t v___x_308_; size_t v___x_309_; uint8_t v___x_310_; 
v___x_308_ = l_Lean_instHashableExtraModUse_hash(v_x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_306_, v___x_309_, v_x_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_311_, v_x_312_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_315_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
lean_ctor_set(v___x_322_, 2, v___x_321_);
lean_ctor_set(v___x_322_, 3, v___x_321_);
lean_ctor_set(v___x_322_, 4, v___x_321_);
lean_ctor_set(v___x_322_, 5, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_cls_337_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_338_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13));
v___x_339_ = l_Lean_Name_append(v___x_338_, v_cls_337_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_350_, uint8_t v_isMeta_351_, lean_object* v_hint_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_env_361_; uint8_t v_isExporting_362_; lean_object* v_entry_363_; lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_359_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_360_ = lean_st_ref_get(v___y_357_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v_isExporting_362_ = lean_ctor_get_uint8(v_env_361_, sizeof(void*)*8);
lean_dec_ref(v_env_361_);
lean_inc(v_mod_350_);
v_entry_363_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_363_, 0, v_mod_350_);
lean_ctor_set_uint8(v_entry_363_, sizeof(void*)*1, v_isExporting_362_);
lean_ctor_set_uint8(v_entry_363_, sizeof(void*)*1 + 1, v_isMeta_351_);
v___x_364_ = lean_st_ref_get(v___y_357_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_367_ = lean_box(1);
v___x_368_ = lean_box(0);
v___x_414_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_359_, v___x_366_, v_env_365_, v___x_367_, v___x_368_);
v___x_415_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_414_, v_entry_363_);
lean_dec(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v_toCold_416_; lean_object* v_options_417_; uint8_t v_hasTrace_418_; 
v_toCold_416_ = lean_ctor_get(v___y_356_, 0);
v_options_417_ = lean_ctor_get(v_toCold_416_, 2);
v_hasTrace_418_ = lean_ctor_get_uint8(v_options_417_, sizeof(void*)*1);
if (v_hasTrace_418_ == 0)
{
lean_dec(v_hint_352_);
lean_dec(v_mod_350_);
v___y_370_ = v___y_353_;
v___y_371_ = v___y_355_;
v___y_372_ = v___y_357_;
goto v___jp_369_;
}
else
{
lean_object* v_inheritedTraceOptions_419_; lean_object* v_cls_420_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_inheritedTraceOptions_419_ = lean_ctor_get(v_toCold_416_, 11);
v_cls_420_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14);
v___x_443_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_419_, v_options_417_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v_hint_352_);
lean_dec(v_mod_350_);
v___y_370_ = v___y_353_;
v___y_371_ = v___y_355_;
v___y_372_ = v___y_357_;
goto v___jp_369_;
}
else
{
lean_object* v___x_444_; lean_object* v___y_446_; 
v___x_444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
if (v_isExporting_362_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_446_ = v___x_453_;
goto v___jp_445_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
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
v___x_449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
if (v_isMeta_351_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_429_ = v___x_450_;
v___y_430_ = v___x_451_;
goto v___jp_428_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
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
v___x_425_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_420_, v___x_424_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_snd_427_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v_snd_427_ = lean_ctor_get(v_a_426_, 1);
lean_inc(v_snd_427_);
lean_dec(v_a_426_);
v___y_370_ = v_snd_427_;
v___y_371_ = v___y_355_;
v___y_372_ = v___y_357_;
goto v___jp_369_;
}
else
{
lean_dec_ref_known(v_entry_363_, 1);
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
v___x_433_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_MessageData_ofName(v_mod_350_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_Name_isAnonymous(v_hint_352_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_439_ = l_Lean_MessageData_ofName(v_hint_352_);
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
lean_dec(v_hint_352_);
v___x_441_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11);
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
lean_dec_ref_known(v_entry_363_, 1);
lean_dec(v_hint_352_);
lean_dec(v_mod_350_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_353_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
v___jp_369_:
{
lean_object* v___x_373_; lean_object* v_toEnvExtension_374_; lean_object* v_env_375_; lean_object* v_nextMacroScope_376_; lean_object* v_ngen_377_; lean_object* v_auxDeclNGen_378_; lean_object* v_traceState_379_; lean_object* v_recordedDeps_380_; lean_object* v_messages_381_; lean_object* v_infoState_382_; lean_object* v_snapshotTasks_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_412_; 
v___x_373_ = lean_st_ref_take(v___y_372_);
v_toEnvExtension_374_ = lean_ctor_get(v___x_366_, 0);
v_env_375_ = lean_ctor_get(v___x_373_, 0);
v_nextMacroScope_376_ = lean_ctor_get(v___x_373_, 1);
v_ngen_377_ = lean_ctor_get(v___x_373_, 2);
v_auxDeclNGen_378_ = lean_ctor_get(v___x_373_, 3);
v_traceState_379_ = lean_ctor_get(v___x_373_, 4);
v_recordedDeps_380_ = lean_ctor_get(v___x_373_, 6);
v_messages_381_ = lean_ctor_get(v___x_373_, 7);
v_infoState_382_ = lean_ctor_get(v___x_373_, 8);
v_snapshotTasks_383_ = lean_ctor_get(v___x_373_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_373_, 5);
lean_dec(v_unused_413_);
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_412_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snapshotTasks_383_);
lean_inc(v_infoState_382_);
lean_inc(v_messages_381_);
lean_inc(v_recordedDeps_380_);
lean_inc(v_traceState_379_);
lean_inc(v_auxDeclNGen_378_);
lean_inc(v_ngen_377_);
lean_inc(v_nextMacroScope_376_);
lean_inc(v_env_375_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_412_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_asyncMode_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v_asyncMode_387_ = lean_ctor_get(v_toEnvExtension_374_, 2);
v___x_388_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_366_, v_env_375_, v_entry_363_, v_asyncMode_387_, v___x_368_);
v___x_389_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 5, v___x_389_);
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_391_ = v___x_385_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_376_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_377_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_378_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_379_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_recordedDeps_380_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_messages_381_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_infoState_382_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_snapshotTasks_383_);
v___x_391_ = v_reuseFailAlloc_411_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_mctx_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_409_; 
v___x_392_ = lean_st_ref_put(v___y_372_, v___x_391_);
v___x_393_ = lean_st_ref_take(v___y_371_);
v_mctx_394_ = lean_ctor_get(v___x_393_, 0);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_393_, 2);
v_postponed_396_ = lean_ctor_get(v___x_393_, 3);
v_diag_397_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_410_);
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_diag_397_);
lean_inc(v_postponed_396_);
lean_inc(v_zetaDeltaFVarIds_395_);
lean_inc(v_mctx_394_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_mctx_394_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_397_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_st_ref_put(v___y_371_, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_401_);
lean_ctor_set(v___x_406_, 1, v___y_370_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_box(0);
return v___x_471_;
}
else
{
lean_object* v_key_472_; lean_object* v_value_473_; lean_object* v_tail_474_; uint8_t v___x_475_; 
v_key_472_ = lean_ctor_get(v_x_470_, 0);
v_value_473_ = lean_ctor_get(v_x_470_, 1);
v_tail_474_ = lean_ctor_get(v_x_470_, 2);
v___x_475_ = lean_name_eq(v_key_472_, v_a_469_);
if (v___x_475_ == 0)
{
v_x_470_ = v_tail_474_;
goto _start;
}
else
{
lean_object* v___x_477_; 
lean_inc(v_value_473_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_value_473_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_a_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_buckets_483_; lean_object* v___x_484_; uint64_t v___y_486_; 
v_buckets_483_ = lean_ctor_get(v_m_481_, 1);
v___x_484_ = lean_array_get_size(v_buckets_483_);
if (lean_obj_tag(v_a_482_) == 0)
{
uint64_t v___x_500_; 
v___x_500_ = 1723ULL;
v___y_486_ = v___x_500_;
goto v___jp_485_;
}
else
{
uint64_t v_hash_501_; 
v_hash_501_ = lean_ctor_get_uint64(v_a_482_, sizeof(void*)*2);
v___y_486_ = v_hash_501_;
goto v___jp_485_;
}
v___jp_485_:
{
uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v_fold_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_487_ = 32ULL;
v___x_488_ = lean_uint64_shift_right(v___y_486_, v___x_487_);
v_fold_489_ = lean_uint64_xor(v___y_486_, v___x_488_);
v___x_490_ = 16ULL;
v___x_491_ = lean_uint64_shift_right(v_fold_489_, v___x_490_);
v___x_492_ = lean_uint64_xor(v_fold_489_, v___x_491_);
v___x_493_ = lean_uint64_to_usize(v___x_492_);
v___x_494_ = lean_usize_of_nat(v___x_484_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_sub(v___x_494_, v___x_495_);
v___x_497_ = lean_usize_land(v___x_493_, v___x_496_);
v___x_498_ = lean_array_uget_borrowed(v_buckets_483_, v___x_497_);
v___x_499_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_482_, v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_m_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_505_, lean_object* v_declName_506_, lean_object* v_as_507_, size_t v_sz_508_, size_t v_i_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_509_, v_sz_508_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_declName_506_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_b_510_);
lean_ctor_set(v___x_518_, 1, v___y_511_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v_modules_521_; lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v_toImport_525_; lean_object* v_module_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
v___x_520_ = l_Lean_Environment_header(v___x_505_);
v_modules_521_ = lean_ctor_get(v___x_520_, 3);
lean_inc_ref(v_modules_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_523_ = lean_array_uget_borrowed(v_as_507_, v_i_509_);
v___x_524_ = lean_array_get(v___x_522_, v_modules_521_, v_a_523_);
lean_dec_ref(v_modules_521_);
v_toImport_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_ref(v_toImport_525_);
lean_dec(v___x_524_);
v_module_526_ = lean_ctor_get(v_toImport_525_, 0);
lean_inc(v_module_526_);
lean_dec_ref(v_toImport_525_);
v___x_527_ = lean_box(0);
v___x_528_ = 0;
lean_inc(v_declName_506_);
v___x_529_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_526_, v___x_528_, v_declName_506_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v_snd_531_; size_t v___x_532_; size_t v___x_533_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v_snd_531_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_snd_531_);
lean_dec(v_a_530_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_509_, v___x_532_);
v_i_509_ = v___x_533_;
v_b_510_ = v___x_527_;
v___y_511_ = v_snd_531_;
goto _start;
}
else
{
lean_dec(v_declName_506_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_535_, lean_object* v_declName_536_, lean_object* v_as_537_, lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_b_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_548_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_535_, v_declName_536_, v_as_537_, v_sz_boxed_547_, v_i_boxed_548_, v_b_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec_ref(v_as_537_);
lean_dec_ref(v___x_535_);
return v_res_549_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_HashMap_instInhabited___redArg();
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_553_, uint8_t v_isMeta_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_env_567_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___x_592_; 
v___x_561_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_562_ = lean_st_ref_get(v___y_559_);
v_env_567_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_567_);
lean_dec(v___x_562_);
v___x_592_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_567_, v_declName_553_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_dec_ref(v_env_567_);
lean_dec(v_declName_553_);
goto v___jp_563_;
}
else
{
lean_object* v_val_593_; lean_object* v___x_594_; lean_object* v_modules_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_val_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = l_Lean_Environment_header(v_env_567_);
v_modules_595_ = lean_ctor_get(v___x_594_, 3);
lean_inc_ref(v_modules_595_);
lean_dec_ref(v___x_594_);
v___x_596_ = lean_array_get_size(v_modules_595_);
v___x_597_ = lean_nat_dec_lt(v_val_593_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec_ref(v_modules_595_);
lean_dec(v_val_593_);
lean_dec_ref(v_env_567_);
lean_dec(v_declName_553_);
goto v___jp_563_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___y_601_; 
v___x_598_ = lean_array_fget(v_modules_595_, v_val_593_);
lean_dec(v_val_593_);
lean_dec_ref(v_modules_595_);
v___x_599_ = lean_st_ref_get(v___y_559_);
if (v_isMeta_554_ == 0)
{
lean_dec(v___x_599_);
v___y_601_ = v_isMeta_554_;
goto v___jp_600_;
}
else
{
lean_object* v_env_614_; uint8_t v___x_615_; 
v_env_614_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_599_);
lean_inc(v_declName_553_);
v___x_615_ = l_Lean_isMarkedMeta(v_env_614_, v_declName_553_);
if (v___x_615_ == 0)
{
v___y_601_ = v_isMeta_554_;
goto v___jp_600_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
v___y_601_ = v___x_616_;
goto v___jp_600_;
}
}
v___jp_600_:
{
lean_object* v_toImport_602_; lean_object* v_module_603_; lean_object* v___x_604_; 
v_toImport_602_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_toImport_602_);
lean_dec(v___x_598_);
v_module_603_ = lean_ctor_get(v_toImport_602_, 0);
lean_inc(v_module_603_);
lean_dec_ref(v_toImport_602_);
lean_inc(v_declName_553_);
v___x_604_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_603_, v___y_601_, v_declName_553_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_snd_606_ = lean_ctor_get(v_a_605_, 1);
lean_inc(v_snd_606_);
lean_dec(v_a_605_);
v___x_607_ = l_Lean_indirectModUseExt;
v___x_608_ = lean_box(1);
v___x_609_ = lean_box(0);
lean_inc_ref(v_env_567_);
v___x_610_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_561_, v___x_607_, v_env_567_, v___x_608_, v___x_609_);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_610_, v_declName_553_);
lean_dec(v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_569_ = v_snd_606_;
v___y_570_ = v___x_612_;
goto v___jp_568_;
}
else
{
lean_object* v_val_613_; 
v_val_613_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v___x_611_, 1);
v___y_569_ = v_snd_606_;
v___y_570_ = v_val_613_;
goto v___jp_568_;
}
}
else
{
lean_dec_ref(v_env_567_);
lean_dec(v_declName_553_);
return v___x_604_;
}
}
}
}
v___jp_563_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___y_555_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
v___jp_568_:
{
lean_object* v___x_571_; size_t v_sz_572_; size_t v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v_sz_572_ = lean_array_size(v___y_570_);
v___x_573_ = ((size_t)0ULL);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_567_, v_declName_553_, v___y_570_, v_sz_572_, v___x_573_, v___x_571_, v___y_569_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_env_567_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_591_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_591_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v_snd_579_ = lean_ctor_get(v_a_575_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_a_575_, 0);
lean_dec(v_unused_590_);
v___x_581_ = v_a_575_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_dec(v_a_575_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_571_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_579_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_584_);
v___x_586_ = v___x_577_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_617_, lean_object* v_isMeta_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
uint8_t v_isMeta_boxed_625_; lean_object* v_res_626_; 
v_isMeta_boxed_625_ = lean_unbox(v_isMeta_618_);
v_res_626_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_617_, v_isMeta_boxed_625_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___y_642_; lean_object* v_f_646_; uint8_t v___x_647_; 
v_f_646_ = l_Lean_Expr_getAppFn(v_e_634_);
v___x_647_ = l_Lean_Expr_isConst(v_f_646_);
if (v___x_647_ == 0)
{
lean_dec_ref(v_f_646_);
lean_dec_ref(v_e_634_);
v___y_642_ = v___y_635_;
goto v___jp_641_;
}
else
{
lean_object* v_declName_648_; lean_object* v___x_649_; lean_object* v_env_650_; uint8_t v___x_651_; 
v_declName_648_ = l_Lean_Expr_constName_x21(v_f_646_);
lean_dec_ref(v_f_646_);
v___x_649_ = lean_st_ref_get(v___y_639_);
v_env_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_env_650_);
lean_dec(v___x_649_);
lean_inc(v_declName_648_);
v___x_651_ = l_Lean_Meta_isCoeDecl(v_env_650_, v_declName_648_);
if (v___x_651_ == 0)
{
lean_dec(v_declName_648_);
lean_dec_ref(v_e_634_);
v___y_642_ = v___y_635_;
goto v___jp_641_;
}
else
{
lean_object* v___x_652_; 
lean_inc(v_declName_648_);
lean_inc_ref(v_e_634_);
v___x_652_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_634_, v_declName_648_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; uint8_t v___x_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = 0;
v___x_655_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_653_, v___x_654_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_708_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v_snd_657_ = lean_ctor_get(v_a_656_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_a_656_, 0);
lean_dec(v_unused_709_);
v___x_659_ = v_a_656_;
v_isShared_660_ = v_isSharedCheck_708_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_dec(v_a_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_708_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; 
lean_inc_ref(v_e_634_);
v___x_661_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_634_, v___x_654_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_699_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_699_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_699_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_699_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
if (lean_obj_tag(v_a_662_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_698_; 
v_val_666_ = lean_ctor_get(v_a_662_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_662_);
if (v_isSharedCheck_698_ == 0)
{
v___x_668_ = v_a_662_;
v_isShared_669_ = v_isSharedCheck_698_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_val_666_);
lean_dec(v_a_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_698_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___y_671_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_683_ = lean_name_eq(v_declName_648_, v___x_682_);
lean_dec(v_declName_648_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_e_634_);
v___y_671_ = v_snd_657_;
goto v___jp_670_;
}
else
{
lean_object* v_dummy_684_; lean_object* v_nargs_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_dummy_684_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_685_ = l_Lean_Expr_getAppNumArgs(v_e_634_);
lean_inc(v_nargs_685_);
v___x_686_ = lean_mk_array(v_nargs_685_, v_dummy_684_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v_nargs_685_, v___x_687_);
lean_dec(v_nargs_685_);
v___x_689_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_634_, v___x_686_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(2u);
v___x_691_ = lean_array_get_size(v___x_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_689_);
v___y_671_ = v_snd_657_;
goto v___jp_670_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = lean_array_fget(v___x_689_, v___x_690_);
lean_dec_ref(v___x_689_);
v___x_694_ = l_Lean_Expr_getAppFn(v___x_693_);
lean_dec(v___x_693_);
v___x_695_ = l_Lean_Expr_isConst(v___x_694_);
if (v___x_695_ == 0)
{
lean_dec_ref(v___x_694_);
v___y_671_ = v_snd_657_;
goto v___jp_670_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Lean_Expr_constName_x21(v___x_694_);
lean_dec_ref(v___x_694_);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_snd_657_);
v___y_671_ = v___x_697_;
goto v___jp_670_;
}
}
}
v___jp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = l_Lean_Expr_headBeta(v_val_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_672_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_681_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___y_671_);
lean_ctor_set(v___x_659_, 0, v___x_674_);
v___x_676_ = v___x_659_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___y_671_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_676_);
v___x_678_ = v___x_664_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_664_);
lean_dec(v_a_662_);
lean_del_object(v___x_659_);
lean_dec(v_declName_648_);
lean_dec_ref(v_e_634_);
v___y_642_ = v_snd_657_;
goto v___jp_641_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_659_);
lean_dec(v_snd_657_);
lean_dec(v_declName_648_);
lean_dec_ref(v_e_634_);
v_a_700_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_661_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_661_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_declName_648_);
lean_dec_ref(v_e_634_);
v_a_710_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_655_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_655_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_declName_648_);
lean_dec(v___y_635_);
lean_dec_ref(v_e_634_);
v_a_718_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_652_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_652_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___y_642_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_expandCoe___lam__1(v_e_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_735_);
v___x_743_ = lean_apply_8(v_k_734_, v_b_737_, v___y_735_, v___y_736_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, lean_box(0));
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_744_, v___y_745_, v___y_746_, v_b_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_745_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_754_, uint8_t v_bi_755_, lean_object* v_type_756_, lean_object* v_k_757_, uint8_t v_kind_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; 
lean_inc(v___y_759_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_766_, 0, v_k_757_);
lean_closure_set(v___f_766_, 1, v___y_759_);
lean_closure_set(v___f_766_, 2, v___y_760_);
v___x_767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_754_, v_bi_755_, v_type_756_, v___f_766_, v_kind_758_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_767_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_784_, lean_object* v_bi_785_, lean_object* v_type_786_, lean_object* v_k_787_, lean_object* v_kind_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
uint8_t v_bi_boxed_796_; uint8_t v_kind_boxed_797_; lean_object* v_res_798_; 
v_bi_boxed_796_ = lean_unbox(v_bi_785_);
v_kind_boxed_797_ = lean_unbox(v_kind_788_);
v_res_798_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_784_, v_bi_boxed_796_, v_type_786_, v_k_787_, v_kind_boxed_797_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_789_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_799_);
lean_ctor_set(v___x_806_, 1, v___y_800_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_816_, lean_object* v_type_817_, lean_object* v_val_818_, lean_object* v_k_819_, uint8_t v_nondep_820_, uint8_t v_kind_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___f_829_; lean_object* v___x_830_; 
lean_inc(v___y_822_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_829_, 0, v_k_819_);
lean_closure_set(v___f_829_, 1, v___y_822_);
lean_closure_set(v___f_829_, 2, v___y_823_);
v___x_830_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_816_, v_type_817_, v_val_818_, v___f_829_, v_nondep_820_, v_kind_821_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_830_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_830_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_847_, lean_object* v_type_848_, lean_object* v_val_849_, lean_object* v_k_850_, lean_object* v_nondep_851_, lean_object* v_kind_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_nondep_boxed_860_; uint8_t v_kind_boxed_861_; lean_object* v_res_862_; 
v_nondep_boxed_860_ = lean_unbox(v_nondep_851_);
v_kind_boxed_861_ = lean_unbox(v_kind_852_);
v_res_862_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_847_, v_type_848_, v_val_849_, v_k_850_, v_nondep_boxed_860_, v_kind_boxed_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_863_, lean_object* v_b_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_dec(v_b_864_);
lean_dec_ref(v_a_863_);
return v_x_865_;
}
else
{
lean_object* v_key_866_; lean_object* v_value_867_; lean_object* v_tail_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_880_; 
v_key_866_ = lean_ctor_get(v_x_865_, 0);
v_value_867_ = lean_ctor_get(v_x_865_, 1);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_870_ = v_x_865_;
v_isShared_871_ = v_isSharedCheck_880_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_tail_868_);
lean_inc(v_value_867_);
lean_inc(v_key_866_);
lean_dec(v_x_865_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_880_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_ExprStructEq_beq(v_key_866_, v_a_863_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_863_, v_b_864_, v_tail_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 2, v___x_873_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_key_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_value_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v_value_867_);
lean_dec(v_key_866_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_b_864_);
lean_ctor_set(v___x_870_, 0, v_a_863_);
v___x_878_ = v___x_870_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_863_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_b_864_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_tail_868_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
uint8_t v___x_883_; 
v___x_883_ = 0;
return v___x_883_;
}
else
{
lean_object* v_key_884_; lean_object* v_tail_885_; uint8_t v___x_886_; 
v_key_884_ = lean_ctor_get(v_x_882_, 0);
v_tail_885_ = lean_ctor_get(v_x_882_, 2);
v___x_886_ = l_Lean_ExprStructEq_beq(v_key_884_, v_a_881_);
if (v___x_886_ == 0)
{
v_x_882_ = v_tail_885_;
goto _start;
}
else
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_888_, v_x_889_);
lean_dec(v_x_889_);
lean_dec_ref(v_a_888_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
return v_x_892_;
}
else
{
lean_object* v_key_894_; lean_object* v_value_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_919_; 
v_key_894_ = lean_ctor_get(v_x_893_, 0);
v_value_895_ = lean_ctor_get(v_x_893_, 1);
v_tail_896_ = lean_ctor_get(v_x_893_, 2);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_919_ == 0)
{
v___x_898_ = v_x_893_;
v_isShared_899_ = v_isSharedCheck_919_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_value_895_);
lean_inc(v_key_894_);
lean_dec(v_x_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_919_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v_fold_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_900_ = lean_array_get_size(v_x_892_);
v___x_901_ = l_Lean_ExprStructEq_hash(v_key_894_);
v___x_902_ = 32ULL;
v___x_903_ = lean_uint64_shift_right(v___x_901_, v___x_902_);
v_fold_904_ = lean_uint64_xor(v___x_901_, v___x_903_);
v___x_905_ = 16ULL;
v___x_906_ = lean_uint64_shift_right(v_fold_904_, v___x_905_);
v___x_907_ = lean_uint64_xor(v_fold_904_, v___x_906_);
v___x_908_ = lean_uint64_to_usize(v___x_907_);
v___x_909_ = lean_usize_of_nat(v___x_900_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_sub(v___x_909_, v___x_910_);
v___x_912_ = lean_usize_land(v___x_908_, v___x_911_);
v___x_913_ = lean_array_uget_borrowed(v_x_892_, v___x_912_);
lean_inc(v___x_913_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 2, v___x_913_);
v___x_915_ = v___x_898_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_key_894_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_value_895_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v___x_913_);
v___x_915_ = v_reuseFailAlloc_918_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_array_uset(v_x_892_, v___x_912_, v___x_915_);
v_x_892_ = v___x_916_;
v_x_893_ = v_tail_896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_920_, lean_object* v_source_921_, lean_object* v_target_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_source_921_);
v___x_924_ = lean_nat_dec_lt(v_i_920_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec_ref(v_source_921_);
lean_dec(v_i_920_);
return v_target_922_;
}
else
{
lean_object* v_es_925_; lean_object* v___x_926_; lean_object* v_source_927_; lean_object* v_target_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_es_925_ = lean_array_fget(v_source_921_, v_i_920_);
v___x_926_ = lean_box(0);
v_source_927_ = lean_array_fset(v_source_921_, v_i_920_, v___x_926_);
v_target_928_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_922_, v_es_925_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_i_920_, v___x_929_);
lean_dec(v_i_920_);
v_i_920_ = v___x_930_;
v_source_921_ = v_source_927_;
v_target_922_ = v_target_928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_932_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_nbuckets_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_933_ = lean_array_get_size(v_data_932_);
v___x_934_ = lean_unsigned_to_nat(2u);
v_nbuckets_935_ = lean_nat_mul(v___x_933_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_box(0);
v___x_938_ = lean_mk_array(v_nbuckets_935_, v___x_937_);
v___x_939_ = lean_array_propagate_mark(v_data_932_, v___x_938_);
v___x_940_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_936_, v_data_932_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_941_, lean_object* v_a_942_, lean_object* v_b_943_){
_start:
{
lean_object* v_size_944_; lean_object* v_buckets_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_988_; 
v_size_944_ = lean_ctor_get(v_m_941_, 0);
v_buckets_945_ = lean_ctor_get(v_m_941_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_m_941_);
if (v_isSharedCheck_988_ == 0)
{
v___x_947_ = v_m_941_;
v_isShared_948_ = v_isSharedCheck_988_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_buckets_945_);
lean_inc(v_size_944_);
lean_dec(v_m_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_988_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v_fold_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v_bkt_962_; uint8_t v___x_963_; 
v___x_949_ = lean_array_get_size(v_buckets_945_);
v___x_950_ = l_Lean_ExprStructEq_hash(v_a_942_);
v___x_951_ = 32ULL;
v___x_952_ = lean_uint64_shift_right(v___x_950_, v___x_951_);
v_fold_953_ = lean_uint64_xor(v___x_950_, v___x_952_);
v___x_954_ = 16ULL;
v___x_955_ = lean_uint64_shift_right(v_fold_953_, v___x_954_);
v___x_956_ = lean_uint64_xor(v_fold_953_, v___x_955_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = lean_usize_of_nat(v___x_949_);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_sub(v___x_958_, v___x_959_);
v___x_961_ = lean_usize_land(v___x_957_, v___x_960_);
v_bkt_962_ = lean_array_uget_borrowed(v_buckets_945_, v___x_961_);
v___x_963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_942_, v_bkt_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v_size_x27_965_; lean_object* v___x_966_; lean_object* v_buckets_x27_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v_size_x27_965_ = lean_nat_add(v_size_944_, v___x_964_);
lean_dec(v_size_944_);
lean_inc(v_bkt_962_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v_a_942_);
lean_ctor_set(v___x_966_, 1, v_b_943_);
lean_ctor_set(v___x_966_, 2, v_bkt_962_);
v_buckets_x27_967_ = lean_array_uset(v_buckets_945_, v___x_961_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_nat_mul(v_size_x27_965_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(3u);
v___x_971_ = lean_nat_div(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_array_get_size(v_buckets_x27_967_);
v___x_973_ = lean_nat_dec_le(v___x_971_, v___x_972_);
lean_dec(v___x_971_);
if (v___x_973_ == 0)
{
lean_object* v_val_974_; lean_object* v___x_976_; 
v_val_974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_967_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_val_974_);
lean_ctor_set(v___x_947_, 0, v_size_x27_965_);
v___x_976_ = v___x_947_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_val_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v___x_979_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_buckets_x27_967_);
lean_ctor_set(v___x_947_, 0, v_size_x27_965_);
v___x_979_ = v___x_947_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_size_x27_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_buckets_x27_967_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v___x_981_; lean_object* v_buckets_x27_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
lean_inc(v_bkt_962_);
v___x_981_ = lean_box(0);
v_buckets_x27_982_ = lean_array_uset(v_buckets_945_, v___x_961_, v___x_981_);
v___x_983_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_942_, v_b_943_, v_bkt_962_);
v___x_984_ = lean_array_uset(v_buckets_x27_982_, v___x_961_, v___x_983_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_984_);
v___x_986_ = v___x_947_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_size_944_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_989_, lean_object* v_e_990_, lean_object* v_fst_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = lean_st_ref_take(v_a_989_);
v___x_994_ = lean_box(0);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_993_, v_e_990_, v_fst_991_);
v___x_996_ = lean_st_ref_put(v_a_989_, v___x_995_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_997_, lean_object* v_e_998_, lean_object* v_fst_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_997_, v_e_998_, v_fst_999_);
lean_dec(v_a_997_);
return v_res_1001_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = l_Lean_maxRecDepthErrorMessage;
v___x_1008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1010_ = l_Lean_MessageData_ofFormat(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1012_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1013_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_ref_1014_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___y_1031_; lean_object* v_toCold_1048_; lean_object* v_currRecDepth_1049_; lean_object* v_ref_1050_; uint16_t v_optionFlags_1051_; uint8_t v_suppressElabErrors_1052_; uint8_t v_isRecordingDeps_1053_; lean_object* v_maxRecDepth_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_toCold_1048_ = lean_ctor_get(v___y_1027_, 0);
v_currRecDepth_1049_ = lean_ctor_get(v___y_1027_, 1);
v_ref_1050_ = lean_ctor_get(v___y_1027_, 2);
v_optionFlags_1051_ = lean_ctor_get_uint16(v___y_1027_, sizeof(void*)*3);
v_suppressElabErrors_1052_ = lean_ctor_get_uint8(v___y_1027_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1053_ = lean_ctor_get_uint8(v___y_1027_, sizeof(void*)*3 + 3);
v_maxRecDepth_1059_ = lean_ctor_get(v_toCold_1048_, 3);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v_maxRecDepth_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_eq(v_currRecDepth_1049_, v_maxRecDepth_1059_);
if (v___x_1062_ == 0)
{
goto v___jp_1054_;
}
else
{
lean_object* v___x_1063_; 
lean_dec(v___y_1024_);
lean_dec_ref(v_x_1022_);
lean_inc(v_ref_1050_);
v___x_1063_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1050_);
v___y_1031_ = v___x_1063_;
goto v___jp_1030_;
}
}
else
{
goto v___jp_1054_;
}
v___jp_1030_:
{
if (lean_obj_tag(v___y_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___y_1031_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___y_1031_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___y_1031_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___y_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___y_1031_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___y_1031_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___y_1031_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___y_1031_);
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
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
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
v___jp_1054_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_currRecDepth_1049_, v___x_1055_);
lean_inc(v_ref_1050_);
lean_inc_ref(v_toCold_1048_);
v___x_1057_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1057_, 0, v_toCold_1048_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
lean_ctor_set(v___x_1057_, 2, v_ref_1050_);
lean_ctor_set_uint16(v___x_1057_, sizeof(void*)*3, v_optionFlags_1051_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*3 + 2, v_suppressElabErrors_1052_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*3 + 3, v_isRecordingDeps_1053_);
lean_inc(v___y_1028_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1023_);
v___x_1058_ = lean_apply_7(v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___x_1057_, v___y_1028_, lean_box(0));
v___y_1031_ = v___x_1058_;
goto v___jp_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1065_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1073_, lean_object* v_x_1074_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
else
{
lean_object* v_key_1076_; lean_object* v_value_1077_; lean_object* v_tail_1078_; uint8_t v___x_1079_; 
v_key_1076_ = lean_ctor_get(v_x_1074_, 0);
v_value_1077_ = lean_ctor_get(v_x_1074_, 1);
v_tail_1078_ = lean_ctor_get(v_x_1074_, 2);
v___x_1079_ = l_Lean_ExprStructEq_beq(v_key_1076_, v_a_1073_);
if (v___x_1079_ == 0)
{
v_x_1074_ = v_tail_1078_;
goto _start;
}
else
{
lean_object* v___x_1081_; 
lean_inc(v_value_1077_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_value_1077_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1082_, v_x_1083_);
lean_dec(v_x_1083_);
lean_dec_ref(v_a_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_buckets_1087_; lean_object* v___x_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v_fold_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_buckets_1087_ = lean_ctor_get(v_m_1085_, 1);
v___x_1088_ = lean_array_get_size(v_buckets_1087_);
v___x_1089_ = l_Lean_ExprStructEq_hash(v_a_1086_);
v___x_1090_ = 32ULL;
v___x_1091_ = lean_uint64_shift_right(v___x_1089_, v___x_1090_);
v_fold_1092_ = lean_uint64_xor(v___x_1089_, v___x_1091_);
v___x_1093_ = 16ULL;
v___x_1094_ = lean_uint64_shift_right(v_fold_1092_, v___x_1093_);
v___x_1095_ = lean_uint64_xor(v_fold_1092_, v___x_1094_);
v___x_1096_ = lean_uint64_to_usize(v___x_1095_);
v___x_1097_ = lean_usize_of_nat(v___x_1088_);
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_sub(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_usize_land(v___x_1096_, v___x_1099_);
v___x_1101_ = lean_array_uget_borrowed(v_buckets_1087_, v___x_1100_);
v___x_1102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1086_, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1103_, v_a_1104_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_m_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_apply_1(v_x_1107_, lean_box(0));
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___y_1108_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1117_, v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1126_, lean_object* v_pre_1127_, lean_object* v_post_1128_, lean_object* v_usedLetOnly_1129_, lean_object* v_skipConstInApp_1130_, lean_object* v_skipInstances_1131_, lean_object* v_body_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_usedLetOnly_boxed_1141_; uint8_t v_skipConstInApp_boxed_1142_; uint8_t v_skipInstances_boxed_1143_; lean_object* v_res_1144_; 
v_usedLetOnly_boxed_1141_ = lean_unbox(v_usedLetOnly_1129_);
v_skipConstInApp_boxed_1142_ = lean_unbox(v_skipConstInApp_1130_);
v_skipInstances_boxed_1143_ = lean_unbox(v_skipInstances_1131_);
v_res_1144_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1126_, v_pre_1127_, v_post_1128_, v_usedLetOnly_boxed_1141_, v_skipConstInApp_boxed_1142_, v_skipInstances_boxed_1143_, v_body_1132_, v_x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1134_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1148_, lean_object* v_pre_1149_, lean_object* v_post_1150_, uint8_t v_usedLetOnly_1151_, uint8_t v_skipConstInApp_1152_, uint8_t v_skipInstances_1153_, lean_object* v_body_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_array_push(v_fvars_1148_, v_x_1155_);
v___x_1164_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1149_, v_post_1150_, v_usedLetOnly_1151_, v_skipConstInApp_1152_, v_skipInstances_1153_, v___x_1163_, v_body_1154_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1165_, lean_object* v_pre_1166_, lean_object* v_post_1167_, lean_object* v_usedLetOnly_1168_, lean_object* v_skipConstInApp_1169_, lean_object* v_skipInstances_1170_, lean_object* v_body_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_usedLetOnly_boxed_1180_; uint8_t v_skipConstInApp_boxed_1181_; uint8_t v_skipInstances_boxed_1182_; lean_object* v_res_1183_; 
v_usedLetOnly_boxed_1180_ = lean_unbox(v_usedLetOnly_1168_);
v_skipConstInApp_boxed_1181_ = lean_unbox(v_skipConstInApp_1169_);
v_skipInstances_boxed_1182_ = lean_unbox(v_skipInstances_1170_);
v_res_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1165_, v_pre_1166_, v_post_1167_, v_usedLetOnly_boxed_1180_, v_skipConstInApp_boxed_1181_, v_skipInstances_boxed_1182_, v_body_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1173_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1184_, lean_object* v_post_1185_, uint8_t v_usedLetOnly_1186_, uint8_t v_skipConstInApp_1187_, uint8_t v_skipInstances_1188_, lean_object* v_e_1189_, lean_object* v_a_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
lean_inc_ref(v_post_1185_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
lean_inc_ref(v_e_1189_);
v___x_1197_ = lean_apply_7(v_post_1185_, v_e_1189_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, lean_box(0));
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1229_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1229_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1229_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_fst_1202_; lean_object* v_snd_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1228_; 
v_fst_1202_ = lean_ctor_get(v_a_1198_, 0);
v_snd_1203_ = lean_ctor_get(v_a_1198_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_a_1198_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1205_ = v_a_1198_;
v_isShared_1206_ = v_isSharedCheck_1228_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snd_1203_);
lean_inc(v_fst_1202_);
lean_dec(v_a_1198_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1228_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___y_1208_; 
switch(lean_obj_tag(v_fst_1202_))
{
case 0:
{
lean_object* v_e_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_del_object(v___x_1205_);
lean_del_object(v___x_1200_);
lean_dec_ref(v_e_1189_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1184_);
v_e_1215_ = lean_ctor_get(v_fst_1202_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_fst_1202_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_fst_1202_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_e_1215_);
lean_dec(v_fst_1202_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_e_1215_);
lean_ctor_set(v___x_1219_, 1, v_snd_1203_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
case 1:
{
lean_object* v_e_1224_; lean_object* v___x_1225_; 
lean_del_object(v___x_1205_);
lean_del_object(v___x_1200_);
lean_dec_ref(v_e_1189_);
v_e_1224_ = lean_ctor_get(v_fst_1202_, 0);
lean_inc_ref(v_e_1224_);
lean_dec_ref_known(v_fst_1202_, 1);
v___x_1225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1184_, v_post_1185_, v_usedLetOnly_1186_, v_skipConstInApp_1187_, v_skipInstances_1188_, v_e_1224_, v_a_1190_, v_snd_1203_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1225_;
}
default: 
{
lean_object* v_e_x3f_1226_; 
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1184_);
v_e_x3f_1226_ = lean_ctor_get(v_fst_1202_, 0);
lean_inc(v_e_x3f_1226_);
lean_dec_ref_known(v_fst_1202_, 1);
if (lean_obj_tag(v_e_x3f_1226_) == 0)
{
v___y_1208_ = v_e_1189_;
goto v___jp_1207_;
}
else
{
lean_object* v_val_1227_; 
lean_dec_ref(v_e_1189_);
v_val_1227_ = lean_ctor_get(v_e_x3f_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_e_x3f_1226_, 1);
v___y_1208_ = v_val_1227_;
goto v___jp_1207_;
}
}
}
v___jp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___y_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___y_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_snd_1203_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1210_);
v___x_1212_ = v___x_1200_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_e_1189_);
lean_dec_ref(v_post_1185_);
lean_dec_ref(v_pre_1184_);
v_a_1230_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1197_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1197_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1238_, lean_object* v_post_1239_, uint8_t v_usedLetOnly_1240_, uint8_t v_skipConstInApp_1241_, uint8_t v_skipInstances_1242_, lean_object* v_fvars_1243_, lean_object* v_e_1244_, lean_object* v_a_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
if (lean_obj_tag(v_e_1244_) == 6)
{
lean_object* v_binderName_1252_; lean_object* v_binderType_1253_; lean_object* v_body_1254_; uint8_t v_binderInfo_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_binderName_1252_ = lean_ctor_get(v_e_1244_, 0);
lean_inc(v_binderName_1252_);
v_binderType_1253_ = lean_ctor_get(v_e_1244_, 1);
lean_inc_ref(v_binderType_1253_);
v_body_1254_ = lean_ctor_get(v_e_1244_, 2);
lean_inc_ref(v_body_1254_);
v_binderInfo_1255_ = lean_ctor_get_uint8(v_e_1244_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1244_, 3);
v___x_1256_ = lean_box(v_usedLetOnly_1240_);
v___x_1257_ = lean_box(v_skipConstInApp_1241_);
v___x_1258_ = lean_box(v_skipInstances_1242_);
lean_inc_ref(v_post_1239_);
lean_inc_ref(v_pre_1238_);
lean_inc_ref(v_fvars_1243_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1259_, 0, v_fvars_1243_);
lean_closure_set(v___f_1259_, 1, v_pre_1238_);
lean_closure_set(v___f_1259_, 2, v_post_1239_);
lean_closure_set(v___f_1259_, 3, v___x_1256_);
lean_closure_set(v___f_1259_, 4, v___x_1257_);
lean_closure_set(v___f_1259_, 5, v___x_1258_);
lean_closure_set(v___f_1259_, 6, v_body_1254_);
v___x_1260_ = lean_expr_instantiate_rev(v_binderType_1253_, v_fvars_1243_);
lean_dec_ref(v_fvars_1243_);
lean_dec_ref(v_binderType_1253_);
v___x_1261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1238_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1260_, v_a_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v_fst_1263_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_fst_1263_);
v_snd_1264_ = lean_ctor_get(v_a_1262_, 1);
lean_inc(v_snd_1264_);
lean_dec(v_a_1262_);
v___x_1265_ = 0;
v___x_1266_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1252_, v_binderInfo_1255_, v_fst_1263_, v___f_1259_, v___x_1265_, v_a_1245_, v_snd_1264_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1266_;
}
else
{
lean_dec_ref(v___f_1259_);
lean_dec(v_binderName_1252_);
return v___x_1261_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_expr_instantiate_rev(v_e_1244_, v_fvars_1243_);
lean_dec_ref(v_e_1244_);
lean_inc_ref(v_post_1239_);
lean_inc_ref(v_pre_1238_);
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1238_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1267_, v_a_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; uint8_t v___x_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v_fst_1270_ = lean_ctor_get(v_a_1269_, 0);
lean_inc(v_fst_1270_);
v_snd_1271_ = lean_ctor_get(v_a_1269_, 1);
lean_inc(v_snd_1271_);
lean_dec(v_a_1269_);
v___x_1272_ = 0;
v___x_1273_ = 1;
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1243_, v_fst_1270_, v___x_1272_, v_usedLetOnly_1240_, v___x_1272_, v___x_1273_, v___x_1274_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec_ref(v_fvars_1243_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1238_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v_a_1276_, v_a_1245_, v_snd_1271_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1277_;
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_snd_1271_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_a_1278_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1275_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1275_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
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
else
{
lean_dec_ref(v_fvars_1243_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1286_, lean_object* v_pre_1287_, lean_object* v_post_1288_, uint8_t v_usedLetOnly_1289_, uint8_t v_skipConstInApp_1290_, uint8_t v_skipInstances_1291_, lean_object* v_body_1292_, lean_object* v_x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_array_push(v_fvars_1286_, v_x_1293_);
v___x_1302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1287_, v_post_1288_, v_usedLetOnly_1289_, v_skipConstInApp_1290_, v_skipInstances_1291_, v___x_1301_, v_body_1292_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1303_, lean_object* v_pre_1304_, lean_object* v_post_1305_, lean_object* v_usedLetOnly_1306_, lean_object* v_skipConstInApp_1307_, lean_object* v_skipInstances_1308_, lean_object* v_body_1309_, lean_object* v_x_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_usedLetOnly_boxed_1318_; uint8_t v_skipConstInApp_boxed_1319_; uint8_t v_skipInstances_boxed_1320_; lean_object* v_res_1321_; 
v_usedLetOnly_boxed_1318_ = lean_unbox(v_usedLetOnly_1306_);
v_skipConstInApp_boxed_1319_ = lean_unbox(v_skipConstInApp_1307_);
v_skipInstances_boxed_1320_ = lean_unbox(v_skipInstances_1308_);
v_res_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1303_, v_pre_1304_, v_post_1305_, v_usedLetOnly_boxed_1318_, v_skipConstInApp_boxed_1319_, v_skipInstances_boxed_1320_, v_body_1309_, v_x_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1311_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1322_, lean_object* v_post_1323_, uint8_t v_usedLetOnly_1324_, uint8_t v_skipConstInApp_1325_, uint8_t v_skipInstances_1326_, lean_object* v_fvars_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
if (lean_obj_tag(v_e_1328_) == 8)
{
lean_object* v_declName_1336_; lean_object* v_type_1337_; lean_object* v_value_1338_; lean_object* v_body_1339_; uint8_t v_nondep_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_declName_1336_ = lean_ctor_get(v_e_1328_, 0);
lean_inc(v_declName_1336_);
v_type_1337_ = lean_ctor_get(v_e_1328_, 1);
lean_inc_ref(v_type_1337_);
v_value_1338_ = lean_ctor_get(v_e_1328_, 2);
lean_inc_ref(v_value_1338_);
v_body_1339_ = lean_ctor_get(v_e_1328_, 3);
lean_inc_ref(v_body_1339_);
v_nondep_1340_ = lean_ctor_get_uint8(v_e_1328_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1328_, 4);
v___x_1341_ = lean_box(v_usedLetOnly_1324_);
v___x_1342_ = lean_box(v_skipConstInApp_1325_);
v___x_1343_ = lean_box(v_skipInstances_1326_);
lean_inc_ref_n(v_post_1323_, 2);
lean_inc_ref_n(v_pre_1322_, 2);
lean_inc_ref(v_fvars_1327_);
v___f_1344_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1344_, 0, v_fvars_1327_);
lean_closure_set(v___f_1344_, 1, v_pre_1322_);
lean_closure_set(v___f_1344_, 2, v_post_1323_);
lean_closure_set(v___f_1344_, 3, v___x_1341_);
lean_closure_set(v___f_1344_, 4, v___x_1342_);
lean_closure_set(v___f_1344_, 5, v___x_1343_);
lean_closure_set(v___f_1344_, 6, v_body_1339_);
v___x_1345_ = lean_expr_instantiate_rev(v_type_1337_, v_fvars_1327_);
lean_dec_ref(v_type_1337_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1322_, v_post_1323_, v_usedLetOnly_1324_, v_skipConstInApp_1325_, v_skipInstances_1326_, v___x_1345_, v_a_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_fst_1348_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v_a_1347_, 1);
lean_inc(v_snd_1349_);
lean_dec(v_a_1347_);
v___x_1350_ = lean_expr_instantiate_rev(v_value_1338_, v_fvars_1327_);
lean_dec_ref(v_fvars_1327_);
lean_dec_ref(v_value_1338_);
v___x_1351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1322_, v_post_1323_, v_usedLetOnly_1324_, v_skipConstInApp_1325_, v_skipInstances_1326_, v___x_1350_, v_a_1329_, v_snd_1349_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_fst_1353_; lean_object* v_snd_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v_fst_1353_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_fst_1353_);
v_snd_1354_ = lean_ctor_get(v_a_1352_, 1);
lean_inc(v_snd_1354_);
lean_dec(v_a_1352_);
v___x_1355_ = 0;
v___x_1356_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1336_, v_fst_1348_, v_fst_1353_, v___f_1344_, v_nondep_1340_, v___x_1355_, v_a_1329_, v_snd_1354_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1356_;
}
else
{
lean_dec(v_fst_1348_);
lean_dec_ref(v___f_1344_);
lean_dec(v_declName_1336_);
return v___x_1351_;
}
}
else
{
lean_dec_ref(v___f_1344_);
lean_dec_ref(v_value_1338_);
lean_dec(v_declName_1336_);
lean_dec_ref(v_fvars_1327_);
lean_dec_ref(v_post_1323_);
lean_dec_ref(v_pre_1322_);
return v___x_1346_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_expr_instantiate_rev(v_e_1328_, v_fvars_1327_);
lean_dec_ref(v_e_1328_);
lean_inc_ref(v_post_1323_);
lean_inc_ref(v_pre_1322_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1322_, v_post_1323_, v_usedLetOnly_1324_, v_skipConstInApp_1325_, v_skipInstances_1326_, v___x_1357_, v_a_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; uint8_t v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v_fst_1360_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v_a_1359_, 1);
lean_inc(v_snd_1361_);
lean_dec(v_a_1359_);
v___x_1362_ = 0;
v___x_1363_ = 1;
v___x_1364_ = l_Lean_Meta_mkLetFVars(v_fvars_1327_, v_fst_1360_, v_usedLetOnly_1324_, v___x_1362_, v___x_1363_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec_ref(v_fvars_1327_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1322_, v_post_1323_, v_usedLetOnly_1324_, v_skipConstInApp_1325_, v_skipInstances_1326_, v_a_1365_, v_a_1329_, v_snd_1361_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1366_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_snd_1361_);
lean_dec_ref(v_post_1323_);
lean_dec_ref(v_pre_1322_);
v_a_1367_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1364_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1364_);
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
lean_dec_ref(v_fvars_1327_);
lean_dec_ref(v_post_1323_);
lean_dec_ref(v_pre_1322_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1375_, lean_object* v_post_1376_, uint8_t v_usedLetOnly_1377_, uint8_t v_skipConstInApp_1378_, uint8_t v_skipInstances_1379_, size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_bs_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_lt(v_i_1381_, v_sz_1380_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_post_1376_);
lean_dec_ref(v_pre_1375_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_bs_1382_);
lean_ctor_set(v___x_1391_, 1, v___y_1384_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
else
{
lean_object* v_v_1393_; lean_object* v___x_1394_; lean_object* v_bs_x27_1395_; lean_object* v___x_1396_; 
v_v_1393_ = lean_array_uget(v_bs_1382_, v_i_1381_);
v___x_1394_ = lean_unsigned_to_nat(0u);
v_bs_x27_1395_ = lean_array_uset(v_bs_1382_, v_i_1381_, v___x_1394_);
lean_inc_ref(v_post_1376_);
lean_inc_ref(v_pre_1375_);
v___x_1396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1375_, v_post_1376_, v_usedLetOnly_1377_, v_skipConstInApp_1378_, v_skipInstances_1379_, v_v_1393_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v_fst_1398_ = lean_ctor_get(v_a_1397_, 0);
lean_inc(v_fst_1398_);
v_snd_1399_ = lean_ctor_get(v_a_1397_, 1);
lean_inc(v_snd_1399_);
lean_dec(v_a_1397_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_i_1381_, v___x_1400_);
v___x_1402_ = lean_array_uset(v_bs_x27_1395_, v_i_1381_, v_fst_1398_);
v_i_1381_ = v___x_1401_;
v_bs_1382_ = v___x_1402_;
v___y_1384_ = v_snd_1399_;
goto _start;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_bs_x27_1395_);
lean_dec_ref(v_post_1376_);
lean_dec_ref(v_pre_1375_);
v_a_1404_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1396_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1396_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1412_, lean_object* v_post_1413_, uint8_t v_usedLetOnly_1414_, uint8_t v_skipConstInApp_1415_, uint8_t v_skipInstances_1416_, lean_object* v___x_1417_, lean_object* v___y_1418_, lean_object* v_b_1419_, lean_object* v_a_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1412_, v_post_1413_, v_usedLetOnly_1414_, v_skipConstInApp_1415_, v_skipInstances_1416_, v___x_1417_, v___y_1418_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1446_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1445_; 
v_fst_1432_ = lean_ctor_get(v_a_1428_, 0);
v_snd_1433_ = lean_ctor_get(v_a_1428_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1435_ = v_a_1428_;
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1433_);
lean_inc(v_fst_1432_);
lean_dec(v_a_1428_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = lean_array_fset(v_b_1419_, v_a_1420_, v_fst_1432_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1433_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1440_);
v___x_1442_ = v___x_1430_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_b_1419_);
v_a_1447_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1427_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1427_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1455_, lean_object* v_post_1456_, lean_object* v_usedLetOnly_1457_, lean_object* v_skipConstInApp_1458_, lean_object* v_skipInstances_1459_, lean_object* v___x_1460_, lean_object* v___y_1461_, lean_object* v_b_1462_, lean_object* v_a_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_usedLetOnly_boxed_1470_; uint8_t v_skipConstInApp_boxed_1471_; uint8_t v_skipInstances_boxed_1472_; lean_object* v_res_1473_; 
v_usedLetOnly_boxed_1470_ = lean_unbox(v_usedLetOnly_1457_);
v_skipConstInApp_boxed_1471_ = lean_unbox(v_skipConstInApp_1458_);
v_skipInstances_boxed_1472_ = lean_unbox(v_skipInstances_1459_);
v_res_1473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1455_, v_post_1456_, v_usedLetOnly_boxed_1470_, v_skipConstInApp_boxed_1471_, v_skipInstances_boxed_1472_, v___x_1460_, v___y_1461_, v_b_1462_, v_a_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v_a_1463_);
lean_dec(v___y_1461_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1474_, lean_object* v___x_1475_, lean_object* v_pre_1476_, lean_object* v_post_1477_, uint8_t v_usedLetOnly_1478_, uint8_t v_skipConstInApp_1479_, uint8_t v_skipInstances_1480_, lean_object* v_a_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___y_1491_; uint8_t v___x_1525_; 
v___x_1525_ = lean_nat_dec_lt(v_a_1481_, v_upperBound_1474_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_post_1477_);
lean_dec_ref(v_pre_1476_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_b_1482_);
lean_ctor_set(v___x_1526_, 1, v___y_1484_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_array_fget_borrowed(v_b_1482_, v_a_1481_);
v___x_1529_ = lean_array_get_size(v___x_1475_);
v___x_1530_ = lean_nat_dec_lt(v_a_1481_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___f_1534_; 
lean_inc(v___x_1528_);
v___x_1531_ = lean_box(v_usedLetOnly_1478_);
v___x_1532_ = lean_box(v_skipConstInApp_1479_);
v___x_1533_ = lean_box(v_skipInstances_1480_);
lean_inc(v_a_1481_);
lean_inc(v___y_1483_);
lean_inc_ref(v_post_1477_);
lean_inc_ref(v_pre_1476_);
v___f_1534_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1534_, 0, v_pre_1476_);
lean_closure_set(v___f_1534_, 1, v_post_1477_);
lean_closure_set(v___f_1534_, 2, v___x_1531_);
lean_closure_set(v___f_1534_, 3, v___x_1532_);
lean_closure_set(v___f_1534_, 4, v___x_1533_);
lean_closure_set(v___f_1534_, 5, v___x_1528_);
lean_closure_set(v___f_1534_, 6, v___y_1483_);
lean_closure_set(v___f_1534_, 7, v_b_1482_);
lean_closure_set(v___f_1534_, 8, v_a_1481_);
v___y_1491_ = v___f_1534_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1535_; uint8_t v_isInstance_1536_; 
v___x_1535_ = lean_array_fget_borrowed(v___x_1475_, v_a_1481_);
v_isInstance_1536_ = lean_ctor_get_uint8(v___x_1535_, sizeof(void*)*1 + 4);
if (v_isInstance_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___f_1540_; 
lean_inc(v___x_1528_);
v___x_1537_ = lean_box(v_usedLetOnly_1478_);
v___x_1538_ = lean_box(v_skipConstInApp_1479_);
v___x_1539_ = lean_box(v_skipInstances_1480_);
lean_inc(v_a_1481_);
lean_inc(v___y_1483_);
lean_inc_ref(v_post_1477_);
lean_inc_ref(v_pre_1476_);
v___f_1540_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1540_, 0, v_pre_1476_);
lean_closure_set(v___f_1540_, 1, v_post_1477_);
lean_closure_set(v___f_1540_, 2, v___x_1537_);
lean_closure_set(v___f_1540_, 3, v___x_1538_);
lean_closure_set(v___f_1540_, 4, v___x_1539_);
lean_closure_set(v___f_1540_, 5, v___x_1528_);
lean_closure_set(v___f_1540_, 6, v___y_1483_);
lean_closure_set(v___f_1540_, 7, v_b_1482_);
lean_closure_set(v___f_1540_, 8, v_a_1481_);
v___y_1491_ = v___f_1540_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1541_; lean_object* v___f_1542_; 
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_b_1482_);
v___f_1542_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1542_, 0, v___x_1541_);
v___y_1491_ = v___f_1542_;
goto v___jp_1490_;
}
}
}
v___jp_1490_:
{
lean_object* v___x_1492_; 
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
v___x_1492_ = lean_apply_6(v___y_1491_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, lean_box(0));
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1516_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1516_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1516_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_fst_1497_; 
v_fst_1497_ = lean_ctor_get(v_a_1493_, 0);
lean_inc(v_fst_1497_);
if (lean_obj_tag(v_fst_1497_) == 0)
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_post_1477_);
lean_dec_ref(v_pre_1476_);
v_snd_1498_ = lean_ctor_get(v_a_1493_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_a_1493_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_a_1493_, 0);
lean_dec(v_unused_1510_);
v___x_1500_ = v_a_1493_;
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_a_1493_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1509_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_a_1502_; lean_object* v___x_1504_; 
v_a_1502_ = lean_ctor_get(v_fst_1497_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v_fst_1497_, 1);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_a_1502_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1498_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1504_);
v___x_1506_ = v___x_1495_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_snd_1511_; lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_del_object(v___x_1495_);
v_snd_1511_ = lean_ctor_get(v_a_1493_, 1);
lean_inc(v_snd_1511_);
lean_dec(v_a_1493_);
v_a_1512_ = lean_ctor_get(v_fst_1497_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v_fst_1497_, 1);
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_nat_add(v_a_1481_, v___x_1513_);
lean_dec(v_a_1481_);
v_a_1481_ = v___x_1514_;
v_b_1482_ = v_a_1512_;
v___y_1484_ = v_snd_1511_;
goto _start;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1481_);
lean_dec_ref(v_post_1477_);
lean_dec_ref(v_pre_1476_);
v_a_1517_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1492_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1492_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1543_, lean_object* v_pre_1544_, lean_object* v_post_1545_, uint8_t v_usedLetOnly_1546_, uint8_t v_skipConstInApp_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_f_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; 
if (lean_obj_tag(v_x_1548_) == 5)
{
lean_object* v_fn_1614_; lean_object* v_arg_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_fn_1614_ = lean_ctor_get(v_x_1548_, 0);
lean_inc_ref(v_fn_1614_);
v_arg_1615_ = lean_ctor_get(v_x_1548_, 1);
lean_inc_ref(v_arg_1615_);
lean_dec_ref_known(v_x_1548_, 2);
v___x_1616_ = lean_array_set(v_x_1549_, v_x_1550_, v_arg_1615_);
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_sub(v_x_1550_, v___x_1617_);
lean_dec(v_x_1550_);
v_x_1548_ = v_fn_1614_;
v_x_1549_ = v___x_1616_;
v_x_1550_ = v___x_1618_;
goto _start;
}
else
{
lean_dec(v_x_1550_);
if (v_skipConstInApp_1547_ == 0)
{
goto v___jp_1609_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Expr_isConst(v_x_1548_);
if (v___x_1620_ == 0)
{
goto v___jp_1609_;
}
else
{
v_f_1559_ = v_x_1548_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v___y_1555_;
v___y_1565_ = v___y_1556_;
goto v___jp_1558_;
}
}
}
v___jp_1558_:
{
if (v_skipInstances_1543_ == 0)
{
size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v_sz_1566_ = lean_array_size(v_x_1549_);
v___x_1567_ = ((size_t)0ULL);
lean_inc_ref(v_post_1545_);
lean_inc_ref(v_pre_1544_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1543_, v_sz_1566_, v___x_1567_, v_x_1549_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v_fst_1570_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fst_1570_);
v_snd_1571_ = lean_ctor_get(v_a_1569_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_a_1569_);
v___x_1572_ = l_Lean_mkAppN(v_f_1559_, v_fst_1570_);
lean_dec(v_fst_1570_);
v___x_1573_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1543_, v___x_1572_, v___y_1560_, v_snd_1571_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1573_;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_f_1559_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
v_a_1574_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1568_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1568_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_array_get_size(v_x_1549_);
lean_inc_ref(v_f_1559_);
v___x_1583_ = l_Lean_Meta_getFunInfoNArgs(v_f_1559_, v___x_1582_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v_paramInfo_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v_paramInfo_1585_ = lean_ctor_get(v_a_1584_, 0);
lean_inc_ref(v_paramInfo_1585_);
lean_dec(v_a_1584_);
v___x_1586_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1545_);
lean_inc_ref(v_pre_1544_);
v___x_1587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1582_, v_paramInfo_1585_, v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1543_, v___x_1586_, v_x_1549_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec_ref(v_paramInfo_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_fst_1589_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_fst_1589_);
v_snd_1590_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_snd_1590_);
lean_dec(v_a_1588_);
v___x_1591_ = l_Lean_mkAppN(v_f_1559_, v_fst_1589_);
lean_dec(v_fst_1589_);
v___x_1592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1543_, v___x_1591_, v___y_1560_, v_snd_1590_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1592_;
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_f_1559_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
v_a_1593_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1587_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1587_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v___y_1561_);
lean_dec_ref(v_f_1559_);
lean_dec_ref(v_x_1549_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
v_a_1601_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1583_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1583_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
v___jp_1609_:
{
lean_object* v___x_1610_; 
lean_inc_ref(v_post_1545_);
lean_inc_ref(v_pre_1544_);
v___x_1610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1543_, v_x_1548_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_fst_1612_; lean_object* v_snd_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v_fst_1612_ = lean_ctor_get(v_a_1611_, 0);
lean_inc(v_fst_1612_);
v_snd_1613_ = lean_ctor_get(v_a_1611_, 1);
lean_inc(v_snd_1613_);
lean_dec(v_a_1611_);
v_f_1559_ = v_fst_1612_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v_snd_1613_;
v___y_1562_ = v___y_1553_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v___y_1555_;
v___y_1565_ = v___y_1556_;
goto v___jp_1558_;
}
else
{
lean_dec_ref(v_x_1549_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1621_, lean_object* v_pre_1622_, lean_object* v_e_1623_, lean_object* v_post_1624_, uint8_t v_usedLetOnly_1625_, uint8_t v_skipConstInApp_1626_, uint8_t v_skipInstances_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Core_checkSystem(v___x_1621_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
lean_inc_ref(v_pre_1622_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc_ref(v_e_1623_);
v___x_1636_ = lean_apply_7(v_pre_1622_, v_e_1623_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1698_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1698_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1698_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_fst_1641_; lean_object* v_snd_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1697_; 
v_fst_1641_ = lean_ctor_get(v_a_1637_, 0);
v_snd_1642_ = lean_ctor_get(v_a_1637_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1644_ = v_a_1637_;
v_isShared_1645_ = v_isSharedCheck_1697_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_snd_1642_);
lean_inc(v_fst_1641_);
lean_dec(v_a_1637_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1697_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___y_1647_; 
switch(lean_obj_tag(v_fst_1641_))
{
case 0:
{
lean_object* v_e_1686_; lean_object* v___x_1688_; 
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_e_1623_);
lean_dec_ref(v_pre_1622_);
v_e_1686_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc_ref(v_e_1686_);
lean_dec_ref_known(v_fst_1641_, 1);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_e_1686_);
v___x_1688_ = v___x_1644_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_e_1686_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_snd_1642_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1688_);
v___x_1690_ = v___x_1639_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
case 1:
{
lean_object* v_e_1693_; lean_object* v___x_1694_; 
lean_del_object(v___x_1644_);
lean_del_object(v___x_1639_);
lean_dec_ref(v_e_1623_);
v_e_1693_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc_ref(v_e_1693_);
lean_dec_ref_known(v_fst_1641_, 1);
v___x_1694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v_e_1693_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1694_;
}
default: 
{
lean_object* v_e_x3f_1695_; 
lean_del_object(v___x_1644_);
lean_del_object(v___x_1639_);
v_e_x3f_1695_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_e_x3f_1695_);
lean_dec_ref_known(v_fst_1641_, 1);
if (lean_obj_tag(v_e_x3f_1695_) == 0)
{
v___y_1647_ = v_e_1623_;
goto v___jp_1646_;
}
else
{
lean_object* v_val_1696_; 
lean_dec_ref(v_e_1623_);
v_val_1696_ = lean_ctor_get(v_e_x3f_1695_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_e_x3f_1695_, 1);
v___y_1647_ = v_val_1696_;
goto v___jp_1646_;
}
}
}
v___jp_1646_:
{
switch(lean_obj_tag(v___y_1647_))
{
case 7:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___x_1648_, v___y_1647_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1649_;
}
case 6:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___x_1650_, v___y_1647_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1651_;
}
case 8:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___x_1652_, v___y_1647_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1653_;
}
case 5:
{
lean_object* v_dummy_1654_; lean_object* v_nargs_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_dummy_1654_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1655_ = l_Lean_Expr_getAppNumArgs(v___y_1647_);
lean_inc(v_nargs_1655_);
v___x_1656_ = lean_mk_array(v_nargs_1655_, v_dummy_1654_);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_sub(v_nargs_1655_, v___x_1657_);
lean_dec(v_nargs_1655_);
v___x_1659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1627_, v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v___y_1647_, v___x_1656_, v___x_1658_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1659_;
}
case 10:
{
lean_object* v_data_1660_; lean_object* v_expr_1661_; lean_object* v___x_1662_; 
v_data_1660_ = lean_ctor_get(v___y_1647_, 0);
v_expr_1661_ = lean_ctor_get(v___y_1647_, 1);
lean_inc_ref(v_expr_1661_);
lean_inc_ref(v_post_1624_);
lean_inc_ref(v_pre_1622_);
v___x_1662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v_expr_1661_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; size_t v___x_1666_; size_t v___x_1667_; uint8_t v___x_1668_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v_fst_1664_ = lean_ctor_get(v_a_1663_, 0);
lean_inc(v_fst_1664_);
v_snd_1665_ = lean_ctor_get(v_a_1663_, 1);
lean_inc(v_snd_1665_);
lean_dec(v_a_1663_);
v___x_1666_ = lean_ptr_addr(v_expr_1661_);
v___x_1667_ = lean_ptr_addr(v_fst_1664_);
v___x_1668_ = lean_usize_dec_eq(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_inc(v_data_1660_);
lean_dec_ref_known(v___y_1647_, 2);
v___x_1669_ = l_Lean_Expr_mdata___override(v_data_1660_, v_fst_1664_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___x_1669_, v___y_1628_, v_snd_1665_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; 
lean_dec(v_fst_1664_);
v___x_1671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___y_1647_, v___y_1628_, v_snd_1665_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1671_;
}
}
else
{
lean_dec_ref_known(v___y_1647_, 2);
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_pre_1622_);
return v___x_1662_;
}
}
case 11:
{
lean_object* v_typeName_1672_; lean_object* v_idx_1673_; lean_object* v_struct_1674_; lean_object* v___x_1675_; 
v_typeName_1672_ = lean_ctor_get(v___y_1647_, 0);
v_idx_1673_ = lean_ctor_get(v___y_1647_, 1);
v_struct_1674_ = lean_ctor_get(v___y_1647_, 2);
lean_inc_ref(v_struct_1674_);
lean_inc_ref(v_post_1624_);
lean_inc_ref(v_pre_1622_);
v___x_1675_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v_struct_1674_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; size_t v___x_1679_; size_t v___x_1680_; uint8_t v___x_1681_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v_fst_1677_ = lean_ctor_get(v_a_1676_, 0);
lean_inc(v_fst_1677_);
v_snd_1678_ = lean_ctor_get(v_a_1676_, 1);
lean_inc(v_snd_1678_);
lean_dec(v_a_1676_);
v___x_1679_ = lean_ptr_addr(v_struct_1674_);
v___x_1680_ = lean_ptr_addr(v_fst_1677_);
v___x_1681_ = lean_usize_dec_eq(v___x_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_inc(v_idx_1673_);
lean_inc(v_typeName_1672_);
lean_dec_ref_known(v___y_1647_, 3);
v___x_1682_ = l_Lean_Expr_proj___override(v_typeName_1672_, v_idx_1673_, v_fst_1677_);
v___x_1683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___x_1682_, v___y_1628_, v_snd_1678_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_fst_1677_);
v___x_1684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___y_1647_, v___y_1628_, v_snd_1678_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1684_;
}
}
else
{
lean_dec_ref_known(v___y_1647_, 3);
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_pre_1622_);
return v___x_1675_;
}
}
default: 
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1622_, v_post_1624_, v_usedLetOnly_1625_, v_skipConstInApp_1626_, v_skipInstances_1627_, v___y_1647_, v___y_1628_, v_snd_1642_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1685_;
}
}
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_e_1623_);
lean_dec_ref(v_pre_1622_);
v_a_1699_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1636_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1636_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___y_1629_);
lean_dec_ref(v_post_1624_);
lean_dec_ref(v_e_1623_);
lean_dec_ref(v_pre_1622_);
v_a_1707_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1635_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1635_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1715_, lean_object* v_pre_1716_, lean_object* v_e_1717_, lean_object* v_post_1718_, lean_object* v_usedLetOnly_1719_, lean_object* v_skipConstInApp_1720_, lean_object* v_skipInstances_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_usedLetOnly_boxed_1729_; uint8_t v_skipConstInApp_boxed_1730_; uint8_t v_skipInstances_boxed_1731_; lean_object* v_res_1732_; 
v_usedLetOnly_boxed_1729_ = lean_unbox(v_usedLetOnly_1719_);
v_skipConstInApp_boxed_1730_ = lean_unbox(v_skipConstInApp_1720_);
v_skipInstances_boxed_1731_ = lean_unbox(v_skipInstances_1721_);
v_res_1732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1715_, v_pre_1716_, v_e_1717_, v_post_1718_, v_usedLetOnly_boxed_1729_, v_skipConstInApp_boxed_1730_, v_skipInstances_boxed_1731_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1722_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1733_, lean_object* v_post_1734_, uint8_t v_usedLetOnly_1735_, uint8_t v_skipConstInApp_1736_, uint8_t v_skipInstances_1737_, lean_object* v_e_1738_, lean_object* v_a_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc(v_a_1739_);
v___x_1746_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1746_, 0, lean_box(0));
lean_closure_set(v___x_1746_, 1, lean_box(0));
lean_closure_set(v___x_1746_, 2, v_a_1739_);
v___x_1747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1746_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1802_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1802_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1802_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1801_; 
v_fst_1752_ = lean_ctor_get(v_a_1748_, 0);
v_snd_1753_ = lean_ctor_get(v_a_1748_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_a_1748_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1755_ = v_a_1748_;
v_isShared_1756_ = v_isSharedCheck_1801_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_inc(v_fst_1752_);
lean_dec(v_a_1748_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1801_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1752_, v_e_1738_);
lean_dec(v_fst_1752_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; 
lean_del_object(v___x_1755_);
lean_del_object(v___x_1750_);
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1759_ = lean_box(v_usedLetOnly_1735_);
v___x_1760_ = lean_box(v_skipConstInApp_1736_);
v___x_1761_ = lean_box(v_skipInstances_1737_);
lean_inc_ref(v_e_1738_);
v___f_1762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1762_, 0, v___x_1758_);
lean_closure_set(v___f_1762_, 1, v_pre_1733_);
lean_closure_set(v___f_1762_, 2, v_e_1738_);
lean_closure_set(v___f_1762_, 3, v_post_1734_);
lean_closure_set(v___f_1762_, 4, v___x_1759_);
lean_closure_set(v___f_1762_, 5, v___x_1760_);
lean_closure_set(v___f_1762_, 6, v___x_1761_);
v___x_1763_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1762_, v_a_1739_, v_snd_1753_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v_fst_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc_n(v_fst_1765_, 2);
v_snd_1766_ = lean_ctor_get(v_a_1764_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_a_1764_);
lean_inc(v_a_1739_);
v___f_1767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1767_, 0, v_a_1739_);
lean_closure_set(v___f_1767_, 1, v_e_1738_);
lean_closure_set(v___f_1767_, 2, v_fst_1765_);
v___x_1768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1767_, v_snd_1766_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1785_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1785_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1785_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_snd_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
v_snd_1773_ = lean_ctor_get(v_a_1769_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_a_1769_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v_a_1769_, 0);
lean_dec(v_unused_1784_);
v___x_1775_ = v_a_1769_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snd_1773_);
lean_dec(v_a_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v_fst_1765_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1765_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_snd_1773_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1778_);
v___x_1780_ = v___x_1771_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_fst_1765_);
v_a_1786_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1768_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1768_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_dec_ref(v_e_1738_);
return v___x_1763_;
}
}
else
{
lean_object* v_val_1794_; lean_object* v___x_1796_; 
lean_dec_ref(v_e_1738_);
lean_dec_ref(v_post_1734_);
lean_dec_ref(v_pre_1733_);
v_val_1794_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v___x_1757_, 1);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_val_1794_);
v___x_1796_ = v___x_1755_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_val_1794_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_snd_1753_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1796_);
v___x_1798_ = v___x_1750_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_e_1738_);
lean_dec_ref(v_post_1734_);
lean_dec_ref(v_pre_1733_);
v_a_1803_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1747_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1747_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1811_, lean_object* v_post_1812_, uint8_t v_usedLetOnly_1813_, uint8_t v_skipConstInApp_1814_, uint8_t v_skipInstances_1815_, lean_object* v_fvars_1816_, lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
if (lean_obj_tag(v_e_1817_) == 7)
{
lean_object* v_binderName_1825_; lean_object* v_binderType_1826_; lean_object* v_body_1827_; uint8_t v_binderInfo_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_binderName_1825_ = lean_ctor_get(v_e_1817_, 0);
lean_inc(v_binderName_1825_);
v_binderType_1826_ = lean_ctor_get(v_e_1817_, 1);
lean_inc_ref(v_binderType_1826_);
v_body_1827_ = lean_ctor_get(v_e_1817_, 2);
lean_inc_ref(v_body_1827_);
v_binderInfo_1828_ = lean_ctor_get_uint8(v_e_1817_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1817_, 3);
v___x_1829_ = lean_box(v_usedLetOnly_1813_);
v___x_1830_ = lean_box(v_skipConstInApp_1814_);
v___x_1831_ = lean_box(v_skipInstances_1815_);
lean_inc_ref(v_post_1812_);
lean_inc_ref(v_pre_1811_);
lean_inc_ref(v_fvars_1816_);
v___f_1832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1832_, 0, v_fvars_1816_);
lean_closure_set(v___f_1832_, 1, v_pre_1811_);
lean_closure_set(v___f_1832_, 2, v_post_1812_);
lean_closure_set(v___f_1832_, 3, v___x_1829_);
lean_closure_set(v___f_1832_, 4, v___x_1830_);
lean_closure_set(v___f_1832_, 5, v___x_1831_);
lean_closure_set(v___f_1832_, 6, v_body_1827_);
v___x_1833_ = lean_expr_instantiate_rev(v_binderType_1826_, v_fvars_1816_);
lean_dec_ref(v_fvars_1816_);
lean_dec_ref(v_binderType_1826_);
v___x_1834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1815_, v___x_1833_, v_a_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_fst_1836_; lean_object* v_snd_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_fst_1836_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_fst_1836_);
v_snd_1837_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1837_);
lean_dec(v_a_1835_);
v___x_1838_ = 0;
v___x_1839_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1825_, v_binderInfo_1828_, v_fst_1836_, v___f_1832_, v___x_1838_, v_a_1818_, v_snd_1837_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1839_;
}
else
{
lean_dec_ref(v___f_1832_);
lean_dec(v_binderName_1825_);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_expr_instantiate_rev(v_e_1817_, v_fvars_1816_);
lean_dec_ref(v_e_1817_);
lean_inc_ref(v_post_1812_);
lean_inc_ref(v_pre_1811_);
v___x_1841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1815_, v___x_1840_, v_a_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v_fst_1843_; lean_object* v_snd_1844_; uint8_t v___x_1845_; uint8_t v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v_fst_1843_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_fst_1843_);
v_snd_1844_ = lean_ctor_get(v_a_1842_, 1);
lean_inc(v_snd_1844_);
lean_dec(v_a_1842_);
v___x_1845_ = 0;
v___x_1846_ = 1;
v___x_1847_ = 1;
v___x_1848_ = l_Lean_Meta_mkForallFVars(v_fvars_1816_, v_fst_1843_, v___x_1845_, v_usedLetOnly_1813_, v___x_1846_, v___x_1847_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec_ref(v_fvars_1816_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1811_, v_post_1812_, v_usedLetOnly_1813_, v_skipConstInApp_1814_, v_skipInstances_1815_, v_a_1849_, v_a_1818_, v_snd_1844_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1850_;
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_snd_1844_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
v_a_1851_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1848_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1848_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1816_);
lean_dec_ref(v_post_1812_);
lean_dec_ref(v_pre_1811_);
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1859_, lean_object* v_pre_1860_, lean_object* v_post_1861_, uint8_t v_usedLetOnly_1862_, uint8_t v_skipConstInApp_1863_, uint8_t v_skipInstances_1864_, lean_object* v_body_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_array_push(v_fvars_1859_, v_x_1866_);
v___x_1875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1860_, v_post_1861_, v_usedLetOnly_1862_, v_skipConstInApp_1863_, v_skipInstances_1864_, v___x_1874_, v_body_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1876_, lean_object* v_post_1877_, lean_object* v_usedLetOnly_1878_, lean_object* v_skipConstInApp_1879_, lean_object* v_skipInstances_1880_, lean_object* v_sz_1881_, lean_object* v_i_1882_, lean_object* v_bs_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_usedLetOnly_boxed_1891_; uint8_t v_skipConstInApp_boxed_1892_; uint8_t v_skipInstances_boxed_1893_; size_t v_sz_boxed_1894_; size_t v_i_boxed_1895_; lean_object* v_res_1896_; 
v_usedLetOnly_boxed_1891_ = lean_unbox(v_usedLetOnly_1878_);
v_skipConstInApp_boxed_1892_ = lean_unbox(v_skipConstInApp_1879_);
v_skipInstances_boxed_1893_ = lean_unbox(v_skipInstances_1880_);
v_sz_boxed_1894_ = lean_unbox_usize(v_sz_1881_);
lean_dec(v_sz_1881_);
v_i_boxed_1895_ = lean_unbox_usize(v_i_1882_);
lean_dec(v_i_1882_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1876_, v_post_1877_, v_usedLetOnly_boxed_1891_, v_skipConstInApp_boxed_1892_, v_skipInstances_boxed_1893_, v_sz_boxed_1894_, v_i_boxed_1895_, v_bs_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1884_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1897_, lean_object* v_post_1898_, lean_object* v_usedLetOnly_1899_, lean_object* v_skipConstInApp_1900_, lean_object* v_skipInstances_1901_, lean_object* v_e_1902_, lean_object* v_a_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
uint8_t v_usedLetOnly_boxed_1910_; uint8_t v_skipConstInApp_boxed_1911_; uint8_t v_skipInstances_boxed_1912_; lean_object* v_res_1913_; 
v_usedLetOnly_boxed_1910_ = lean_unbox(v_usedLetOnly_1899_);
v_skipConstInApp_boxed_1911_ = lean_unbox(v_skipConstInApp_1900_);
v_skipInstances_boxed_1912_ = lean_unbox(v_skipInstances_1901_);
v_res_1913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1897_, v_post_1898_, v_usedLetOnly_boxed_1910_, v_skipConstInApp_boxed_1911_, v_skipInstances_boxed_1912_, v_e_1902_, v_a_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v_a_1903_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1914_, lean_object* v_post_1915_, lean_object* v_usedLetOnly_1916_, lean_object* v_skipConstInApp_1917_, lean_object* v_skipInstances_1918_, lean_object* v_fvars_1919_, lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
uint8_t v_usedLetOnly_boxed_1928_; uint8_t v_skipConstInApp_boxed_1929_; uint8_t v_skipInstances_boxed_1930_; lean_object* v_res_1931_; 
v_usedLetOnly_boxed_1928_ = lean_unbox(v_usedLetOnly_1916_);
v_skipConstInApp_boxed_1929_ = lean_unbox(v_skipConstInApp_1917_);
v_skipInstances_boxed_1930_ = lean_unbox(v_skipInstances_1918_);
v_res_1931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1914_, v_post_1915_, v_usedLetOnly_boxed_1928_, v_skipConstInApp_boxed_1929_, v_skipInstances_boxed_1930_, v_fvars_1919_, v_e_1920_, v_a_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v_a_1921_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1932_, lean_object* v_post_1933_, lean_object* v_usedLetOnly_1934_, lean_object* v_skipConstInApp_1935_, lean_object* v_skipInstances_1936_, lean_object* v_fvars_1937_, lean_object* v_e_1938_, lean_object* v_a_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v_usedLetOnly_boxed_1946_; uint8_t v_skipConstInApp_boxed_1947_; uint8_t v_skipInstances_boxed_1948_; lean_object* v_res_1949_; 
v_usedLetOnly_boxed_1946_ = lean_unbox(v_usedLetOnly_1934_);
v_skipConstInApp_boxed_1947_ = lean_unbox(v_skipConstInApp_1935_);
v_skipInstances_boxed_1948_ = lean_unbox(v_skipInstances_1936_);
v_res_1949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1932_, v_post_1933_, v_usedLetOnly_boxed_1946_, v_skipConstInApp_boxed_1947_, v_skipInstances_boxed_1948_, v_fvars_1937_, v_e_1938_, v_a_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v_a_1939_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1950_, lean_object* v_post_1951_, lean_object* v_usedLetOnly_1952_, lean_object* v_skipConstInApp_1953_, lean_object* v_skipInstances_1954_, lean_object* v_e_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_usedLetOnly_boxed_1963_; uint8_t v_skipConstInApp_boxed_1964_; uint8_t v_skipInstances_boxed_1965_; lean_object* v_res_1966_; 
v_usedLetOnly_boxed_1963_ = lean_unbox(v_usedLetOnly_1952_);
v_skipConstInApp_boxed_1964_ = lean_unbox(v_skipConstInApp_1953_);
v_skipInstances_boxed_1965_ = lean_unbox(v_skipInstances_1954_);
v_res_1966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1950_, v_post_1951_, v_usedLetOnly_boxed_1963_, v_skipConstInApp_boxed_1964_, v_skipInstances_boxed_1965_, v_e_1955_, v_a_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_a_1956_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1967_, lean_object* v_post_1968_, lean_object* v_usedLetOnly_1969_, lean_object* v_skipConstInApp_1970_, lean_object* v_skipInstances_1971_, lean_object* v_fvars_1972_, lean_object* v_e_1973_, lean_object* v_a_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
uint8_t v_usedLetOnly_boxed_1981_; uint8_t v_skipConstInApp_boxed_1982_; uint8_t v_skipInstances_boxed_1983_; lean_object* v_res_1984_; 
v_usedLetOnly_boxed_1981_ = lean_unbox(v_usedLetOnly_1969_);
v_skipConstInApp_boxed_1982_ = lean_unbox(v_skipConstInApp_1970_);
v_skipInstances_boxed_1983_ = lean_unbox(v_skipInstances_1971_);
v_res_1984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1967_, v_post_1968_, v_usedLetOnly_boxed_1981_, v_skipConstInApp_boxed_1982_, v_skipInstances_boxed_1983_, v_fvars_1972_, v_e_1973_, v_a_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v_a_1974_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_1985_, lean_object* v___x_1986_, lean_object* v_pre_1987_, lean_object* v_post_1988_, lean_object* v_usedLetOnly_1989_, lean_object* v_skipConstInApp_1990_, lean_object* v_skipInstances_1991_, lean_object* v_a_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v_usedLetOnly_boxed_2001_; uint8_t v_skipConstInApp_boxed_2002_; uint8_t v_skipInstances_boxed_2003_; lean_object* v_res_2004_; 
v_usedLetOnly_boxed_2001_ = lean_unbox(v_usedLetOnly_1989_);
v_skipConstInApp_boxed_2002_ = lean_unbox(v_skipConstInApp_1990_);
v_skipInstances_boxed_2003_ = lean_unbox(v_skipInstances_1991_);
v_res_2004_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1985_, v___x_1986_, v_pre_1987_, v_post_1988_, v_usedLetOnly_boxed_2001_, v_skipConstInApp_boxed_2002_, v_skipInstances_boxed_2003_, v_a_1992_, v_b_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1994_);
lean_dec_ref(v___x_1986_);
lean_dec(v_upperBound_1985_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2005_, lean_object* v_pre_2006_, lean_object* v_post_2007_, lean_object* v_usedLetOnly_2008_, lean_object* v_skipConstInApp_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v_skipInstances_boxed_2020_; uint8_t v_usedLetOnly_boxed_2021_; uint8_t v_skipConstInApp_boxed_2022_; lean_object* v_res_2023_; 
v_skipInstances_boxed_2020_ = lean_unbox(v_skipInstances_2005_);
v_usedLetOnly_boxed_2021_ = lean_unbox(v_usedLetOnly_2008_);
v_skipConstInApp_boxed_2022_ = lean_unbox(v_skipConstInApp_2009_);
v_res_2023_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2020_, v_pre_2006_, v_post_2007_, v_usedLetOnly_boxed_2021_, v_skipConstInApp_boxed_2022_, v_x_2010_, v_x_2011_, v_x_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2013_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2024_, lean_object* v_x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_apply_1(v_x_2025_, lean_box(0));
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___y_2026_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_x_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2035_, v_x_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_mk_array(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2051_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2051_, 0, lean_box(0));
lean_closure_set(v___x_2051_, 1, lean_box(0));
lean_closure_set(v___x_2051_, 2, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2052_, lean_object* v_pre_2053_, lean_object* v_post_2054_, uint8_t v_usedLetOnly_2055_, uint8_t v_skipConstInApp_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2069_; 
v___x_2063_ = 0;
v___x_2064_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2065_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2064_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v_fst_2067_ = lean_ctor_get(v_a_2066_, 0);
lean_inc(v_fst_2067_);
v_snd_2068_ = lean_ctor_get(v_a_2066_, 1);
lean_inc(v_snd_2068_);
lean_dec(v_a_2066_);
v___x_2069_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2053_, v_post_2054_, v_usedLetOnly_2055_, v_skipConstInApp_2056_, v___x_2063_, v_input_2052_, v_fst_2067_, v_snd_2068_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2091_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v_fst_2071_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_fst_2071_);
v_snd_2072_ = lean_ctor_get(v_a_2070_, 1);
lean_inc(v_snd_2072_);
lean_dec(v_a_2070_);
v___x_2073_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2073_, 0, lean_box(0));
lean_closure_set(v___x_2073_, 1, lean_box(0));
lean_closure_set(v___x_2073_, 2, v_fst_2067_);
v___x_2074_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2073_, v_snd_2072_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2091_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2091_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_snd_2079_ = lean_ctor_get(v_a_2075_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_a_2075_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v_a_2075_, 0);
lean_dec(v_unused_2090_);
v___x_2081_ = v_a_2075_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_dec(v_a_2075_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v_fst_2071_);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_fst_2071_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_snd_2079_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2084_);
v___x_2086_ = v___x_2077_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
else
{
lean_dec(v_fst_2067_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2092_, lean_object* v_pre_2093_, lean_object* v_post_2094_, lean_object* v_usedLetOnly_2095_, lean_object* v_skipConstInApp_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v_usedLetOnly_boxed_2103_; uint8_t v_skipConstInApp_boxed_2104_; lean_object* v_res_2105_; 
v_usedLetOnly_boxed_2103_ = lean_unbox(v_usedLetOnly_2095_);
v_skipConstInApp_boxed_2104_ = lean_unbox(v_skipConstInApp_2096_);
v_res_2105_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2092_, v_pre_2093_, v_post_2094_, v_usedLetOnly_boxed_2103_, v_skipConstInApp_boxed_2104_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___y_2115_; lean_object* v___x_2132_; uint8_t v_transparency_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2132_ = l_Lean_Meta_Context_config(v_a_2109_);
v_transparency_2133_ = lean_ctor_get_uint8(v___x_2132_, 9);
lean_dec_ref(v___x_2132_);
v___f_2134_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2135_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2136_ = 0;
v___x_2137_ = 3;
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2133_, v___x_2137_);
if (v___x_2139_ == 0)
{
lean_object* v_keyedConfig_2140_; uint8_t v_trackZetaDelta_2141_; lean_object* v_zetaDeltaSet_2142_; lean_object* v_lctx_2143_; lean_object* v_localInstances_2144_; lean_object* v_defEqCtx_x3f_2145_; lean_object* v_synthPendingDepth_2146_; lean_object* v_customCanUnfoldPredicate_x3f_2147_; uint8_t v_univApprox_2148_; uint8_t v_inTypeClassResolution_2149_; uint8_t v_cacheInferType_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_keyedConfig_2140_ = lean_ctor_get(v_a_2109_, 0);
v_trackZetaDelta_2141_ = lean_ctor_get_uint8(v_a_2109_, sizeof(void*)*7);
v_zetaDeltaSet_2142_ = lean_ctor_get(v_a_2109_, 1);
v_lctx_2143_ = lean_ctor_get(v_a_2109_, 2);
v_localInstances_2144_ = lean_ctor_get(v_a_2109_, 3);
v_defEqCtx_x3f_2145_ = lean_ctor_get(v_a_2109_, 4);
v_synthPendingDepth_2146_ = lean_ctor_get(v_a_2109_, 5);
v_customCanUnfoldPredicate_x3f_2147_ = lean_ctor_get(v_a_2109_, 6);
v_univApprox_2148_ = lean_ctor_get_uint8(v_a_2109_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2149_ = lean_ctor_get_uint8(v_a_2109_, sizeof(void*)*7 + 2);
v_cacheInferType_2150_ = lean_ctor_get_uint8(v_a_2109_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2140_);
v___x_2151_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2137_, v_keyedConfig_2140_);
lean_inc(v_customCanUnfoldPredicate_x3f_2147_);
lean_inc(v_synthPendingDepth_2146_);
lean_inc(v_defEqCtx_x3f_2145_);
lean_inc_ref(v_localInstances_2144_);
lean_inc_ref(v_lctx_2143_);
lean_inc(v_zetaDeltaSet_2142_);
v___x_2152_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_zetaDeltaSet_2142_);
lean_ctor_set(v___x_2152_, 2, v_lctx_2143_);
lean_ctor_set(v___x_2152_, 3, v_localInstances_2144_);
lean_ctor_set(v___x_2152_, 4, v_defEqCtx_x3f_2145_);
lean_ctor_set(v___x_2152_, 5, v_synthPendingDepth_2146_);
lean_ctor_set(v___x_2152_, 6, v_customCanUnfoldPredicate_x3f_2147_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*7, v_trackZetaDelta_2141_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*7 + 1, v_univApprox_2148_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2149_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*7 + 3, v_cacheInferType_2150_);
v___x_2153_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2108_, v___f_2135_, v___f_2134_, v___x_2136_, v___x_2136_, v___x_2138_, v___x_2152_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec_ref_known(v___x_2152_, 7);
v___y_2115_ = v___x_2153_;
goto v___jp_2114_;
}
else
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2108_, v___f_2135_, v___f_2134_, v___x_2136_, v___x_2136_, v___x_2138_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
v___y_2115_ = v___x_2154_;
goto v___jp_2114_;
}
v___jp_2114_:
{
if (lean_obj_tag(v___y_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_a_2116_ = lean_ctor_get(v___y_2115_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___y_2115_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___y_2115_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___y_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___y_2115_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___y_2115_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___y_2115_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___y_2115_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Meta_expandCoe(v_e_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2162_, lean_object* v_m_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2163_, v_a_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2166_, lean_object* v_m_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2166_, v_m_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_m_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2171_, v_x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
uint8_t v_res_2177_; lean_object* v_r_2178_; 
v_res_2177_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2174_, v_x_2175_, v_x_2176_);
lean_dec_ref(v_x_2176_);
lean_dec_ref(v_x_2175_);
v_r_2178_ = lean_box(v_res_2177_);
return v_r_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2179_, lean_object* v_a_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2180_, v_x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2183_, lean_object* v_a_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2183_, v_a_2184_, v_x_2185_);
lean_dec(v_x_2185_);
lean_dec(v_a_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2187_, lean_object* v___x_2188_, lean_object* v_pre_2189_, lean_object* v_post_2190_, uint8_t v_usedLetOnly_2191_, uint8_t v_skipConstInApp_2192_, uint8_t v_skipInstances_2193_, lean_object* v___x_2194_, lean_object* v_inst_2195_, lean_object* v_R_2196_, lean_object* v_a_2197_, lean_object* v_b_2198_, lean_object* v_c_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2187_, v___x_2188_, v_pre_2189_, v_post_2190_, v_usedLetOnly_2191_, v_skipConstInApp_2192_, v_skipInstances_2193_, v_a_2197_, v_b_2198_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2208_ = _args[0];
lean_object* v___x_2209_ = _args[1];
lean_object* v_pre_2210_ = _args[2];
lean_object* v_post_2211_ = _args[3];
lean_object* v_usedLetOnly_2212_ = _args[4];
lean_object* v_skipConstInApp_2213_ = _args[5];
lean_object* v_skipInstances_2214_ = _args[6];
lean_object* v___x_2215_ = _args[7];
lean_object* v_inst_2216_ = _args[8];
lean_object* v_R_2217_ = _args[9];
lean_object* v_a_2218_ = _args[10];
lean_object* v_b_2219_ = _args[11];
lean_object* v_c_2220_ = _args[12];
lean_object* v___y_2221_ = _args[13];
lean_object* v___y_2222_ = _args[14];
lean_object* v___y_2223_ = _args[15];
lean_object* v___y_2224_ = _args[16];
lean_object* v___y_2225_ = _args[17];
lean_object* v___y_2226_ = _args[18];
lean_object* v___y_2227_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2228_; uint8_t v_skipConstInApp_boxed_2229_; uint8_t v_skipInstances_boxed_2230_; lean_object* v_res_2231_; 
v_usedLetOnly_boxed_2228_ = lean_unbox(v_usedLetOnly_2212_);
v_skipConstInApp_boxed_2229_ = lean_unbox(v_skipConstInApp_2213_);
v_skipInstances_boxed_2230_ = lean_unbox(v_skipInstances_2214_);
v_res_2231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2208_, v___x_2209_, v_pre_2210_, v_post_2211_, v_usedLetOnly_boxed_2228_, v_skipConstInApp_boxed_2229_, v_skipInstances_boxed_2230_, v___x_2215_, v_inst_2216_, v_R_2217_, v_a_2218_, v_b_2219_, v_c_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2221_);
lean_dec(v___x_2215_);
lean_dec_ref(v___x_2209_);
lean_dec(v_upperBound_2208_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2232_, lean_object* v_m_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2233_, v_a_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2236_, lean_object* v_m_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2236_, v_m_2237_, v_a_2238_);
lean_dec_ref(v_a_2238_);
lean_dec_ref(v_m_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2240_, lean_object* v_name_2241_, uint8_t v_bi_2242_, lean_object* v_type_2243_, lean_object* v_k_2244_, uint8_t v_kind_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2241_, v_bi_2242_, v_type_2243_, v_k_2244_, v_kind_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_name_2255_, lean_object* v_bi_2256_, lean_object* v_type_2257_, lean_object* v_k_2258_, lean_object* v_kind_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v_bi_boxed_2267_; uint8_t v_kind_boxed_2268_; lean_object* v_res_2269_; 
v_bi_boxed_2267_ = lean_unbox(v_bi_2256_);
v_kind_boxed_2268_ = lean_unbox(v_kind_2259_);
v_res_2269_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2254_, v_name_2255_, v_bi_boxed_2267_, v_type_2257_, v_k_2258_, v_kind_boxed_2268_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2260_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2270_, lean_object* v_name_2271_, lean_object* v_type_2272_, lean_object* v_val_2273_, lean_object* v_k_2274_, uint8_t v_nondep_2275_, uint8_t v_kind_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2271_, v_type_2272_, v_val_2273_, v_k_2274_, v_nondep_2275_, v_kind_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, lean_object* v_type_2287_, lean_object* v_val_2288_, lean_object* v_k_2289_, lean_object* v_nondep_2290_, lean_object* v_kind_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_nondep_boxed_2299_; uint8_t v_kind_boxed_2300_; lean_object* v_res_2301_; 
v_nondep_boxed_2299_ = lean_unbox(v_nondep_2290_);
v_kind_boxed_2300_ = lean_unbox(v_kind_2291_);
v_res_2301_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2285_, v_name_2286_, v_type_2287_, v_val_2288_, v_k_2289_, v_nondep_boxed_2299_, v_kind_boxed_2300_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2292_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2302_, lean_object* v_ref_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2303_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2310_, lean_object* v_ref_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2310_, v_ref_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2328_, lean_object* v_x_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2328_, v_x_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2338_, lean_object* v_m_2339_, lean_object* v_a_2340_, lean_object* v_b_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2339_, v_a_2340_, v_b_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2344_, v_x_2345_, v_x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_){
_start:
{
size_t v_x_39107__boxed_2352_; uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_x_39107__boxed_2352_ = lean_unbox_usize(v_x_2350_);
lean_dec(v_x_2350_);
v_res_2353_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2348_, v_x_2349_, v_x_39107__boxed_2352_, v_x_2351_);
lean_dec_ref(v_x_2351_);
lean_dec_ref(v_x_2349_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2355_, lean_object* v_a_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2356_, v_x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_a_2360_, lean_object* v_x_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2359_, v_a_2360_, v_x_2361_);
lean_dec(v_x_2361_);
lean_dec_ref(v_a_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2363_, lean_object* v_a_2364_, lean_object* v_x_2365_){
_start:
{
uint8_t v___x_2366_; 
v___x_2366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2364_, v_x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2367_, lean_object* v_a_2368_, lean_object* v_x_2369_){
_start:
{
uint8_t v_res_2370_; lean_object* v_r_2371_; 
v_res_2370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2367_, v_a_2368_, v_x_2369_);
lean_dec(v_x_2369_);
lean_dec_ref(v_a_2368_);
v_r_2371_ = lean_box(v_res_2370_);
return v_r_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2372_, lean_object* v_data_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2375_, lean_object* v_a_2376_, lean_object* v_b_2377_, lean_object* v_x_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2376_, v_b_2377_, v_x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2380_, lean_object* v_keys_2381_, lean_object* v_vals_2382_, lean_object* v_heq_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
_start:
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2381_, v_i_2384_, v_k_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2387_, lean_object* v_keys_2388_, lean_object* v_vals_2389_, lean_object* v_heq_2390_, lean_object* v_i_2391_, lean_object* v_k_2392_){
_start:
{
uint8_t v_res_2393_; lean_object* v_r_2394_; 
v_res_2393_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2387_, v_keys_2388_, v_vals_2389_, v_heq_2390_, v_i_2391_, v_k_2392_);
lean_dec_ref(v_k_2392_);
lean_dec_ref(v_vals_2389_);
lean_dec_ref(v_keys_2388_);
v_r_2394_ = lean_box(v_res_2393_);
return v_r_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2395_, lean_object* v_i_2396_, lean_object* v_source_2397_, lean_object* v_target_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2396_, v_source_2397_, v_target_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2401_, v_x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2404_, lean_object* v_decl_2405_, lean_object* v_ref_2406_){
_start:
{
lean_object* v_defValue_2408_; lean_object* v_descr_2409_; lean_object* v_deprecation_x3f_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_defValue_2408_ = lean_ctor_get(v_decl_2405_, 0);
v_descr_2409_ = lean_ctor_get(v_decl_2405_, 1);
v_deprecation_x3f_2410_ = lean_ctor_get(v_decl_2405_, 2);
v___x_2411_ = lean_alloc_ctor(1, 0, 1);
v___x_2412_ = lean_unbox(v_defValue_2408_);
lean_ctor_set_uint8(v___x_2411_, 0, v___x_2412_);
lean_inc(v_deprecation_x3f_2410_);
lean_inc_ref(v_descr_2409_);
lean_inc_n(v_name_2404_, 2);
v___x_2413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2413_, 0, v_name_2404_);
lean_ctor_set(v___x_2413_, 1, v_ref_2406_);
lean_ctor_set(v___x_2413_, 2, v___x_2411_);
lean_ctor_set(v___x_2413_, 3, v_descr_2409_);
lean_ctor_set(v___x_2413_, 4, v_deprecation_x3f_2410_);
v___x_2414_ = lean_register_option(v_name_2404_, v___x_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v___x_2414_, 0);
lean_dec(v_unused_2423_);
v___x_2416_ = v___x_2414_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_dec(v___x_2414_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
lean_inc(v_defValue_2408_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_name_2404_);
lean_ctor_set(v___x_2418_, 1, v_defValue_2408_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_name_2404_);
v_a_2424_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2414_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2414_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2432_, lean_object* v_decl_2433_, lean_object* v_ref_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2432_, v_decl_2433_, v_ref_2434_);
lean_dec_ref(v_decl_2433_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2452_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2454_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2451_, v___x_2452_, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_ref_2463_; lean_object* v___x_2464_; lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
v_ref_2463_ = lean_ctor_get(v___y_2460_, 2);
v___x_2464_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_inc(v_ref_2463_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_ref_2463_);
lean_ctor_set(v___x_2469_, 1, v_a_2465_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 1);
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2496_, lean_object* v_expectedType_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; 
lean_inc(v_a_2501_);
lean_inc_ref(v_a_2500_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc_ref(v_expr_2496_);
v___x_2503_ = lean_infer_type(v_expr_2496_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc_n(v_a_2504_, 2);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l_Lean_Meta_getLevel(v_a_2504_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
lean_inc_ref(v_expectedType_2497_);
v___x_2507_ = l_Lean_Meta_getLevel(v_expectedType_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_a_2506_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc_ref(v___x_2512_);
v___x_2513_ = l_Lean_mkConst(v___x_2509_, v___x_2512_);
v___x_2514_ = lean_unsigned_to_nat(3u);
v___x_2515_ = lean_mk_empty_array_with_capacity(v___x_2514_);
lean_inc(v_a_2504_);
v___x_2516_ = lean_array_push(v___x_2515_, v_a_2504_);
lean_inc_ref(v_expr_2496_);
v___x_2517_ = lean_array_push(v___x_2516_, v_expr_2496_);
lean_inc_ref(v_expectedType_2497_);
v___x_2518_ = lean_array_push(v___x_2517_, v_expectedType_2497_);
v___x_2519_ = l_Lean_mkAppN(v___x_2513_, v___x_2518_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = lean_box(0);
v___x_2521_ = l_Lean_Meta_trySynthInstance(v___x_2519_, v___x_2520_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2619_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2619_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2619_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
switch(lean_obj_tag(v_a_2522_))
{
case 0:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec_ref_known(v___x_2512_, 2);
lean_dec(v_a_2504_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v___x_2526_ = lean_box(0);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
case 1:
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2524_);
v_a_2530_ = lean_ctor_get(v_a_2522_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2532_ = v_a_2522_;
v_isShared_2533_ = v_isSharedCheck_2614_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v_a_2522_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2614_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2534_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2535_ = l_Lean_mkConst(v___x_2534_, v___x_2512_);
v___x_2536_ = lean_unsigned_to_nat(4u);
v___x_2537_ = lean_mk_empty_array_with_capacity(v___x_2536_);
v___x_2538_ = lean_array_push(v___x_2537_, v_a_2504_);
lean_inc_ref(v_expr_2496_);
v___x_2539_ = lean_array_push(v___x_2538_, v_expr_2496_);
lean_inc_ref(v_expectedType_2497_);
v___x_2540_ = lean_array_push(v___x_2539_, v_expectedType_2497_);
v___x_2541_ = lean_array_push(v___x_2540_, v_a_2530_);
v___x_2542_ = l_Lean_mkAppN(v___x_2535_, v___x_2541_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = l_Lean_Meta_expandCoe(v___x_2542_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2605_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2605_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2605_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_fst_2555_; lean_object* v___x_2556_; 
v_fst_2555_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_a_2501_);
lean_inc_ref(v_a_2500_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_fst_2555_);
v___x_2556_ = lean_infer_type(v_fst_2555_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
lean_inc_ref(v_expectedType_2497_);
v___x_2558_ = l_Lean_Meta_isExprDefEq(v_a_2557_, v_expectedType_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2586_; 
lean_inc(v_fst_2555_);
lean_del_object(v___x_2546_);
lean_del_object(v___x_2532_);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2544_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2587_ = lean_ctor_get(v_a_2544_, 1);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_a_2544_, 0);
lean_dec(v_unused_2588_);
v___x_2562_ = v_a_2544_;
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v_a_2544_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2564_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2565_ = l_Lean_indentExpr(v_expr_2496_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 7);
lean_ctor_set(v___x_2562_, 1, v___x_2565_);
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v___x_2568_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_indentExpr(v_expectedType_2497_);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_indentExpr(v_fst_2555_);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2575_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
goto v___jp_2548_;
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2546_);
lean_dec(v_a_2544_);
lean_del_object(v___x_2532_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2589_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2558_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2558_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_del_object(v___x_2546_);
lean_dec(v_a_2544_);
lean_del_object(v___x_2532_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2597_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2556_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2556_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
v___jp_2548_:
{
lean_object* v___x_2550_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_a_2544_);
v___x_2550_ = v___x_2532_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2544_);
v___x_2550_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2552_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2550_);
v___x_2552_ = v___x_2546_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_del_object(v___x_2532_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2606_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2543_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2543_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
default: 
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_dec_ref_known(v___x_2512_, 2);
lean_dec(v_a_2504_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v___x_2615_ = lean_box(2);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2615_);
v___x_2617_ = v___x_2524_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref_known(v___x_2512_, 2);
lean_dec(v_a_2504_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2620_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2521_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2521_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2504_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2628_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2507_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2507_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_a_2504_);
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2636_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2505_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2505_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_expectedType_2497_);
lean_dec_ref(v_expr_2496_);
v_a_2644_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2503_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2503_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2652_, lean_object* v_expectedType_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2652_, v_expectedType_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2668_, v_msg_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2676_, lean_object* v_expectedType_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2676_, v_expectedType_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2708_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2708_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2708_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
switch(lean_obj_tag(v_a_2684_))
{
case 0:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = lean_box(0);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2688_);
v___x_2690_ = v___x_2686_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
case 1:
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2703_; 
v_a_2692_ = lean_ctor_get(v_a_2684_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2694_ = v_a_2684_;
v_isShared_2695_ = v_isSharedCheck_2703_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v_a_2684_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2703_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_fst_2696_; lean_object* v___x_2698_; 
v_fst_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_fst_2696_);
lean_dec(v_a_2692_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_fst_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_fst_2696_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2698_);
v___x_2700_ = v___x_2686_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
default: 
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2704_ = lean_box(2);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2704_);
v___x_2706_ = v___x_2686_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_a_2709_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2683_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2683_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2717_, lean_object* v_expectedType_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2717_, v_expectedType_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
return v_res_2724_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2733_ = l_Lean_stringToMessageData(v___x_2732_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2736_ = l_Lean_stringToMessageData(v___x_2735_);
return v___x_2736_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
lean_inc(v_a_2744_);
lean_inc_ref(v_a_2743_);
lean_inc(v_a_2742_);
lean_inc_ref(v_a_2741_);
lean_inc_ref(v_expr_2740_);
v___x_2746_ = lean_infer_type(v_expr_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_n(v_a_2747_, 2);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = l_Lean_Meta_getLevel(v_a_2747_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc_n(v_a_2751_, 2);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_mkSort(v_a_2751_);
lean_inc(v_a_2747_);
v___x_2753_ = l_Lean_mkArrow(v_a_2747_, v___x_2752_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2754_);
v___x_2756_ = 0;
v___x_2757_ = lean_box(0);
v___x_2758_ = l_Lean_Meta_mkFreshExprMVar(v___x_2755_, v___x_2756_, v___x_2757_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_n(v_a_2759_, 2);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2760_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_a_2751_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2749_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_inc_ref(v___x_2763_);
v___x_2764_ = l_Lean_Expr_const___override(v___x_2760_, v___x_2763_);
lean_inc(v_a_2747_);
v___x_2765_ = l_Lean_mkAppB(v___x_2764_, v_a_2747_, v_a_2759_);
v___x_2766_ = lean_box(0);
v___x_2767_ = l_Lean_Meta_trySynthInstance(v___x_2765_, v___x_2766_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2854_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2854_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2854_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
if (lean_obj_tag(v_a_2768_) == 1)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2850_; 
lean_del_object(v___x_2770_);
v_a_2772_ = lean_ctor_get(v_a_2768_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_a_2768_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2774_ = v_a_2768_;
v_isShared_2775_ = v_isSharedCheck_2850_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v_a_2768_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2850_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2776_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2777_ = l_Lean_Expr_const___override(v___x_2776_, v___x_2763_);
lean_inc_ref(v_expr_2740_);
lean_inc(v_a_2772_);
v___x_2778_ = l_Lean_mkApp4(v___x_2777_, v_a_2747_, v_a_2759_, v_a_2772_, v_expr_2740_);
v___x_2779_ = l_Lean_Meta_expandCoe(v___x_2778_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2841_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2841_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2841_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_fst_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2839_; 
v_fst_2784_ = lean_ctor_get(v_a_2780_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_a_2780_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v_a_2780_, 1);
lean_dec(v_unused_2840_);
v___x_2786_ = v_a_2780_;
v_isShared_2787_ = v_isSharedCheck_2839_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_fst_2784_);
lean_dec(v_a_2780_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2839_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2795_; 
lean_inc(v_a_2744_);
lean_inc_ref(v_a_2743_);
lean_inc(v_a_2742_);
lean_inc_ref(v_a_2741_);
lean_inc(v_fst_2784_);
v___x_2795_ = lean_infer_type(v_fst_2784_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
lean_inc(v_a_2744_);
lean_inc_ref(v_a_2743_);
lean_inc(v_a_2742_);
lean_inc_ref(v_a_2741_);
v___x_2797_ = lean_whnf(v_a_2796_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_Expr_isForall(v_a_2798_);
lean_dec(v_a_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
lean_del_object(v___x_2782_);
lean_del_object(v___x_2774_);
v___x_2800_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2801_ = l_Lean_indentExpr(v_expr_2740_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 7);
lean_ctor_set(v___x_2786_, 1, v___x_2801_);
lean_ctor_set(v___x_2786_, 0, v___x_2800_);
v___x_2803_ = v___x_2786_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
v___x_2804_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_indentExpr(v_fst_2784_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2809_ = l_Lean_indentExpr(v_a_2772_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_MessageData_hint_x27(v___x_2810_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2807_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2812_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_del_object(v___x_2786_);
lean_dec(v_a_2772_);
lean_dec_ref(v_expr_2740_);
goto v___jp_2788_;
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2786_);
lean_dec(v_fst_2784_);
lean_del_object(v___x_2782_);
lean_del_object(v___x_2774_);
lean_dec(v_a_2772_);
lean_dec_ref(v_expr_2740_);
v_a_2823_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2797_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2797_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2786_);
lean_dec(v_fst_2784_);
lean_del_object(v___x_2782_);
lean_del_object(v___x_2774_);
lean_dec(v_a_2772_);
lean_dec_ref(v_expr_2740_);
v_a_2831_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2795_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2795_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
v___jp_2788_:
{
lean_object* v___x_2790_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_fst_2784_);
v___x_2790_ = v___x_2774_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_fst_2784_);
v___x_2790_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2790_);
v___x_2792_ = v___x_2782_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2774_);
lean_dec(v_a_2772_);
lean_dec_ref(v_expr_2740_);
v_a_2842_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2779_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2779_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v_a_2768_);
lean_dec_ref_known(v___x_2763_, 2);
lean_dec(v_a_2759_);
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2766_);
v___x_2852_ = v___x_2770_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2766_);
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
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref_known(v___x_2763_, 2);
lean_dec(v_a_2759_);
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
v_a_2855_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2767_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2767_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2751_);
lean_dec(v_a_2749_);
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
v_a_2863_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2758_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2758_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2751_);
lean_dec(v_a_2749_);
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
v_a_2871_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2753_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2753_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2749_);
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
v_a_2879_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2750_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2750_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2747_);
lean_dec_ref(v_expr_2740_);
v_a_2887_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2748_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2748_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_expr_2740_);
v_a_2895_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2746_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2746_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
return v_res_2909_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2918_ = l_Lean_stringToMessageData(v___x_2917_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; 
lean_inc(v_a_2926_);
lean_inc_ref(v_a_2925_);
lean_inc(v_a_2924_);
lean_inc_ref(v_a_2923_);
lean_inc_ref(v_expr_2922_);
v___x_2928_ = lean_infer_type(v_expr_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_n(v_a_2929_, 2);
lean_dec_ref_known(v___x_2928_, 1);
v___x_2930_ = l_Lean_Meta_getLevel(v_a_2929_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_n(v_a_2933_, 2);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = l_Lean_mkSort(v_a_2933_);
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
v___x_2936_ = 0;
v___x_2937_ = lean_box(0);
v___x_2938_ = l_Lean_Meta_mkFreshExprMVar(v___x_2935_, v___x_2936_, v___x_2937_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_n(v_a_2939_, 2);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2942_, 0, v_a_2933_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_a_2931_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
lean_inc_ref(v___x_2943_);
v___x_2944_ = l_Lean_Expr_const___override(v___x_2940_, v___x_2943_);
lean_inc(v_a_2929_);
v___x_2945_ = l_Lean_mkAppB(v___x_2944_, v_a_2929_, v_a_2939_);
v___x_2946_ = lean_box(0);
v___x_2947_ = l_Lean_Meta_trySynthInstance(v___x_2945_, v___x_2946_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3034_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_3034_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3034_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
if (lean_obj_tag(v_a_2948_) == 1)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3030_; 
lean_del_object(v___x_2950_);
v_a_2952_ = lean_ctor_get(v_a_2948_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_2948_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2954_ = v_a_2948_;
v_isShared_2955_ = v_isSharedCheck_3030_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v_a_2948_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3030_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2957_ = l_Lean_Expr_const___override(v___x_2956_, v___x_2943_);
lean_inc_ref(v_expr_2922_);
lean_inc(v_a_2952_);
v___x_2958_ = l_Lean_mkApp4(v___x_2957_, v_a_2929_, v_a_2939_, v_a_2952_, v_expr_2922_);
v___x_2959_ = l_Lean_Meta_expandCoe(v___x_2958_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3021_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_3021_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3021_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_fst_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3019_; 
v_fst_2964_ = lean_ctor_get(v_a_2960_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_a_2960_, 1);
lean_dec(v_unused_3020_);
v___x_2966_ = v_a_2960_;
v_isShared_2967_ = v_isSharedCheck_3019_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_fst_2964_);
lean_dec(v_a_2960_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3019_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2975_; 
lean_inc(v_a_2926_);
lean_inc_ref(v_a_2925_);
lean_inc(v_a_2924_);
lean_inc_ref(v_a_2923_);
lean_inc(v_fst_2964_);
v___x_2975_ = lean_infer_type(v_fst_2964_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2977_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
lean_inc(v_a_2926_);
lean_inc_ref(v_a_2925_);
lean_inc(v_a_2924_);
lean_inc_ref(v_a_2923_);
v___x_2977_ = lean_whnf(v_a_2976_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; uint8_t v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = l_Lean_Expr_isSort(v_a_2978_);
lean_dec(v_a_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_del_object(v___x_2962_);
lean_del_object(v___x_2954_);
v___x_2980_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2981_ = l_Lean_indentExpr(v_expr_2922_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set_tag(v___x_2966_, 7);
lean_ctor_set(v___x_2966_, 1, v___x_2981_);
lean_ctor_set(v___x_2966_, 0, v___x_2980_);
v___x_2983_ = v___x_2966_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v___x_2984_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_2985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Lean_indentExpr(v_fst_2964_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_2989_ = l_Lean_indentExpr(v_a_2952_);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = l_Lean_MessageData_hint_x27(v___x_2990_);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2987_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2992_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_del_object(v___x_2966_);
lean_dec(v_a_2952_);
lean_dec_ref(v_expr_2922_);
goto v___jp_2968_;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2966_);
lean_dec(v_fst_2964_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec_ref(v_expr_2922_);
v_a_3003_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2977_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2977_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2966_);
lean_dec(v_fst_2964_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec_ref(v_expr_2922_);
v_a_3011_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2975_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2975_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
v___jp_2968_:
{
lean_object* v___x_2970_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v_fst_2964_);
v___x_2970_ = v___x_2954_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_fst_2964_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2970_);
v___x_2972_ = v___x_2962_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_del_object(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec_ref(v_expr_2922_);
v_a_3022_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2959_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2959_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_a_2948_);
lean_dec_ref_known(v___x_2943_, 2);
lean_dec(v_a_2939_);
lean_dec(v_a_2929_);
lean_dec_ref(v_expr_2922_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2946_);
v___x_3032_ = v___x_2950_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_2946_);
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
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref_known(v___x_2943_, 2);
lean_dec(v_a_2939_);
lean_dec(v_a_2929_);
lean_dec_ref(v_expr_2922_);
v_a_3035_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2947_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2947_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_a_2933_);
lean_dec(v_a_2931_);
lean_dec(v_a_2929_);
lean_dec_ref(v_expr_2922_);
v_a_3043_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2938_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2938_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v_a_2931_);
lean_dec(v_a_2929_);
lean_dec_ref(v_expr_2922_);
v_a_3051_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_2932_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_2932_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec(v_a_2929_);
lean_dec_ref(v_expr_2922_);
v_a_3059_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2930_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_2930_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_expr_2922_);
v_a_3067_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_2928_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_2928_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3082_, lean_object* v___y_3083_){
_start:
{
uint8_t v___x_3085_; 
v___x_3085_ = l_Lean_Expr_hasMVar(v_e_3082_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_e_3082_);
return v___x_3086_;
}
else
{
lean_object* v___x_3087_; lean_object* v_mctx_3088_; lean_object* v___x_3089_; lean_object* v_fst_3090_; lean_object* v_snd_3091_; lean_object* v___x_3092_; lean_object* v_cache_3093_; lean_object* v_zetaDeltaFVarIds_3094_; lean_object* v_postponed_3095_; lean_object* v_diag_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3105_; 
v___x_3087_ = lean_st_ref_get(v___y_3083_);
v_mctx_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc_ref(v_mctx_3088_);
lean_dec(v___x_3087_);
v___x_3089_ = l_Lean_instantiateMVarsCore(v_mctx_3088_, v_e_3082_);
v_fst_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_fst_3090_);
v_snd_3091_ = lean_ctor_get(v___x_3089_, 1);
lean_inc(v_snd_3091_);
lean_dec_ref(v___x_3089_);
v___x_3092_ = lean_st_ref_take(v___y_3083_);
v_cache_3093_ = lean_ctor_get(v___x_3092_, 1);
v_zetaDeltaFVarIds_3094_ = lean_ctor_get(v___x_3092_, 2);
v_postponed_3095_ = lean_ctor_get(v___x_3092_, 3);
v_diag_3096_ = lean_ctor_get(v___x_3092_, 4);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v___x_3092_, 0);
lean_dec(v_unused_3106_);
v___x_3098_ = v___x_3092_;
v_isShared_3099_ = v_isSharedCheck_3105_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_diag_3096_);
lean_inc(v_postponed_3095_);
lean_inc(v_zetaDeltaFVarIds_3094_);
lean_inc(v_cache_3093_);
lean_dec(v___x_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3105_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v_snd_3091_);
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_snd_3091_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_cache_3093_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_zetaDeltaFVarIds_3094_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_postponed_3095_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_diag_3096_);
v___x_3101_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_st_ref_put(v___y_3083_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_fst_3090_);
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3107_, v___y_3108_);
lean_dec(v___y_3108_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3111_, v___y_3113_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___y_3132_; lean_object* v___x_3171_; uint8_t v_transparency_3172_; uint8_t v___x_3173_; uint8_t v___x_3174_; 
v___x_3171_ = l_Lean_Meta_Context_config(v_a_3126_);
v_transparency_3172_ = lean_ctor_get_uint8(v___x_3171_, 9);
lean_dec_ref(v___x_3171_);
v___x_3173_ = 2;
v___x_3174_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3172_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v_keyedConfig_3175_; uint8_t v_trackZetaDelta_3176_; lean_object* v_zetaDeltaSet_3177_; lean_object* v_lctx_3178_; lean_object* v_localInstances_3179_; lean_object* v_defEqCtx_x3f_3180_; lean_object* v_synthPendingDepth_3181_; lean_object* v_customCanUnfoldPredicate_x3f_3182_; uint8_t v_univApprox_3183_; uint8_t v_inTypeClassResolution_3184_; uint8_t v_cacheInferType_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_keyedConfig_3175_ = lean_ctor_get(v_a_3126_, 0);
v_trackZetaDelta_3176_ = lean_ctor_get_uint8(v_a_3126_, sizeof(void*)*7);
v_zetaDeltaSet_3177_ = lean_ctor_get(v_a_3126_, 1);
v_lctx_3178_ = lean_ctor_get(v_a_3126_, 2);
v_localInstances_3179_ = lean_ctor_get(v_a_3126_, 3);
v_defEqCtx_x3f_3180_ = lean_ctor_get(v_a_3126_, 4);
v_synthPendingDepth_3181_ = lean_ctor_get(v_a_3126_, 5);
v_customCanUnfoldPredicate_x3f_3182_ = lean_ctor_get(v_a_3126_, 6);
v_univApprox_3183_ = lean_ctor_get_uint8(v_a_3126_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3184_ = lean_ctor_get_uint8(v_a_3126_, sizeof(void*)*7 + 2);
v_cacheInferType_3185_ = lean_ctor_get_uint8(v_a_3126_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3175_);
v___x_3186_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3173_, v_keyedConfig_3175_);
lean_inc(v_customCanUnfoldPredicate_x3f_3182_);
lean_inc(v_synthPendingDepth_3181_);
lean_inc(v_defEqCtx_x3f_3180_);
lean_inc_ref(v_localInstances_3179_);
lean_inc_ref(v_lctx_3178_);
lean_inc(v_zetaDeltaSet_3177_);
v___x_3187_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v_zetaDeltaSet_3177_);
lean_ctor_set(v___x_3187_, 2, v_lctx_3178_);
lean_ctor_set(v___x_3187_, 3, v_localInstances_3179_);
lean_ctor_set(v___x_3187_, 4, v_defEqCtx_x3f_3180_);
lean_ctor_set(v___x_3187_, 5, v_synthPendingDepth_3181_);
lean_ctor_set(v___x_3187_, 6, v_customCanUnfoldPredicate_x3f_3182_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7, v_trackZetaDelta_3176_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 1, v_univApprox_3183_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3184_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*7 + 3, v_cacheInferType_3185_);
lean_inc(v_a_3129_);
lean_inc_ref(v_a_3128_);
lean_inc(v_a_3127_);
v___x_3188_ = lean_whnf(v_type_3125_, v___x_3187_, v_a_3127_, v_a_3128_, v_a_3129_);
v___y_3132_ = v___x_3188_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3189_; 
lean_inc(v_a_3129_);
lean_inc_ref(v_a_3128_);
lean_inc(v_a_3127_);
lean_inc_ref(v_a_3126_);
v___x_3189_ = lean_whnf(v_type_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
v___y_3132_ = v___x_3189_;
goto v___jp_3131_;
}
v___jp_3131_:
{
if (lean_obj_tag(v___y_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3162_; 
v_a_3133_ = lean_ctor_get(v___y_3132_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___y_3132_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3135_ = v___y_3132_;
v_isShared_3136_ = v_isSharedCheck_3162_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___y_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3162_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
if (lean_obj_tag(v_a_3133_) == 5)
{
lean_object* v_fn_3137_; lean_object* v_arg_3138_; lean_object* v___x_3139_; lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3135_);
v_fn_3137_ = lean_ctor_get(v_a_3133_, 0);
lean_inc_ref(v_fn_3137_);
v_arg_3138_ = lean_ctor_get(v_a_3133_, 1);
lean_inc_ref(v_arg_3138_);
lean_dec_ref_known(v_a_3133_, 2);
v___x_3139_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3137_, v_a_3127_);
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3157_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3157_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3156_; 
v___x_3144_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3138_, v_a_3127_);
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3156_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3156_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_a_3140_);
lean_ctor_set(v___x_3149_, 1, v_a_3145_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 1);
lean_ctor_set(v___x_3142_, 0, v___x_3149_);
v___x_3151_ = v___x_3142_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3153_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3151_);
v___x_3153_ = v___x_3147_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
lean_dec(v_a_3133_);
v___x_3158_ = lean_box(0);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3158_);
v___x_3160_ = v___x_3135_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3163_ = lean_ctor_get(v___y_3132_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___y_3132_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___y_3132_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___y_3132_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_Meta_isTypeApp_x3f(v_type_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Meta_isTypeApp_x3f(v_type_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3239_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
if (lean_obj_tag(v_a_3204_) == 1)
{
lean_object* v_val_3208_; lean_object* v_fst_3209_; lean_object* v___x_3210_; 
lean_del_object(v___x_3206_);
v_val_3208_ = lean_ctor_get(v_a_3204_, 0);
lean_inc(v_val_3208_);
lean_dec_ref_known(v_a_3204_, 1);
v_fst_3209_ = lean_ctor_get(v_val_3208_, 0);
lean_inc(v_fst_3209_);
lean_dec(v_val_3208_);
v___x_3210_ = l_Lean_Meta_isMonad_x3f(v_fst_3209_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3225_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
if (lean_obj_tag(v_a_3211_) == 0)
{
uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v___x_3215_ = 0;
v___x_3216_ = lean_box(v___x_3215_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3216_);
v___x_3218_ = v___x_3213_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
else
{
uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec_ref_known(v_a_3211_, 1);
v___x_3220_ = 1;
v___x_3221_ = lean_box(v___x_3220_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3221_);
v___x_3223_ = v___x_3213_;
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
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_a_3226_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3210_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3210_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_dec(v_a_3204_);
v___x_3234_ = 0;
v___x_3235_ = lean_box(v___x_3234_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3235_);
v___x_3237_ = v___x_3206_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
v_a_3240_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3203_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3203_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_isMonadApp(v_type_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
return v_res_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3255_, lean_object* v_opt_3256_){
_start:
{
lean_object* v_name_3257_; lean_object* v_defValue_3258_; lean_object* v_map_3259_; lean_object* v___x_3260_; 
v_name_3257_ = lean_ctor_get(v_opt_3256_, 0);
v_defValue_3258_ = lean_ctor_get(v_opt_3256_, 1);
v_map_3259_ = lean_ctor_get(v_opts_3255_, 0);
v___x_3260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3259_, v_name_3257_);
if (lean_obj_tag(v___x_3260_) == 0)
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_unbox(v_defValue_3258_);
return v___x_3261_;
}
else
{
lean_object* v_val_3262_; 
v_val_3262_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v___x_3260_, 1);
if (lean_obj_tag(v_val_3262_) == 1)
{
uint8_t v_v_3263_; 
v_v_3263_ = lean_ctor_get_uint8(v_val_3262_, 0);
lean_dec_ref_known(v_val_3262_, 0);
return v_v_3263_;
}
else
{
uint8_t v___x_3264_; 
lean_dec(v_val_3262_);
v___x_3264_ = lean_unbox(v_defValue_3258_);
return v___x_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3265_, lean_object* v_opt_3266_){
_start:
{
uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_res_3267_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3265_, v_opt_3266_);
lean_dec_ref(v_opt_3266_);
lean_dec_ref(v_opts_3265_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v_x_3279_);
return v_res_3285_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = l_Lean_mkBVar(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3308_, lean_object* v_expectedType_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v___y_3316_; uint8_t v___y_3317_; lean_object* v_a_3322_; lean_object* v___y_3326_; lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3740_; 
v___x_3336_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3309_, v_a_3311_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3740_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3740_;
goto v_resetjp_3338_;
}
v___jp_3315_:
{
if (v___y_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v___y_3316_);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___y_3316_);
return v___x_3320_;
}
}
v___jp_3321_:
{
uint8_t v___x_3323_; 
v___x_3323_ = l_Lean_Exception_isInterrupt(v_a_3322_);
if (v___x_3323_ == 0)
{
uint8_t v___x_3324_; 
lean_inc_ref(v_a_3322_);
v___x_3324_ = l_Lean_Exception_isRuntime(v_a_3322_);
v___y_3316_ = v_a_3322_;
v___y_3317_ = v___x_3324_;
goto v___jp_3315_;
}
else
{
v___y_3316_ = v_a_3322_;
v___y_3317_ = v___x_3323_;
goto v___jp_3315_;
}
}
v___jp_3325_:
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3335_; 
v_a_3327_ = lean_ctor_get(v___y_3326_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___y_3326_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3329_ = v___y_3326_;
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___y_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_a_3331_; lean_object* v___x_3333_; 
v_a_3331_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_a_3331_);
lean_dec(v_a_3327_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v_a_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; 
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
lean_inc_ref(v_e_3308_);
v___x_3341_ = lean_infer_type(v_e_3308_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3731_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3342_, v_a_3311_);
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3731_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3731_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; 
lean_inc(v_a_3337_);
v___x_3348_ = l_Lean_Meta_isTypeApp_x3f(v_a_3337_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3722_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3722_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3722_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 1)
{
lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3717_; 
lean_del_object(v___x_3351_);
v_val_3353_ = lean_ctor_get(v_a_3349_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_a_3349_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3355_ = v_a_3349_;
v_isShared_3356_ = v_isSharedCheck_3717_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v_a_3349_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3717_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3716_; 
v_fst_3357_ = lean_ctor_get(v_val_3353_, 0);
v_snd_3358_ = lean_ctor_get(v_val_3353_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_val_3353_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3360_ = v_val_3353_;
v_isShared_3361_ = v_isSharedCheck_3716_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_val_3353_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3716_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; 
lean_inc(v_a_3344_);
v___x_3362_ = l_Lean_Meta_isTypeApp_x3f(v_a_3344_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3707_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3707_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3707_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
if (lean_obj_tag(v_a_3363_) == 1)
{
lean_object* v_val_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3702_; 
lean_del_object(v___x_3365_);
v_val_3367_ = lean_ctor_get(v_a_3363_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_a_3363_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3369_ = v_a_3363_;
v_isShared_3370_ = v_isSharedCheck_3702_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_val_3367_);
lean_dec(v_a_3363_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3702_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3701_; 
v_fst_3371_ = lean_ctor_get(v_val_3367_, 0);
v_snd_3372_ = lean_ctor_get(v_val_3367_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_val_3367_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3374_ = v_val_3367_;
v_isShared_3375_ = v_isSharedCheck_3701_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_snd_3372_);
lean_inc(v_fst_3371_);
lean_dec(v_val_3367_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3701_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Meta_saveState___redArg(v_a_3311_, v_a_3313_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
lean_inc(v_fst_3357_);
lean_inc(v_fst_3371_);
v___x_3378_ = l_Lean_Meta_isExprDefEq(v_fst_3371_, v_fst_3357_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3684_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3684_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3684_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
uint8_t v___x_3383_; 
v___x_3383_ = lean_unbox(v_a_3379_);
lean_dec(v_a_3379_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
lean_dec(v_a_3377_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_del_object(v___x_3339_);
v___x_3384_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3312_);
v___x_3385_ = l_Lean_Meta_autoLift;
v___x_3386_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v___x_3384_, v___x_3385_);
lean_dec_ref(v___x_3384_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3387_ = lean_box(0);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3387_);
v___x_3389_ = v___x_3381_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
else
{
lean_object* v___x_3391_; 
lean_del_object(v___x_3381_);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
lean_inc(v_fst_3371_);
v___x_3391_ = lean_infer_type(v_fst_3371_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
v___x_3393_ = lean_whnf(v_a_3392_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
if (lean_obj_tag(v_a_3394_) == 7)
{
lean_object* v_binderType_3395_; 
v_binderType_3395_ = lean_ctor_get(v_a_3394_, 1);
if (lean_obj_tag(v_binderType_3395_) == 3)
{
lean_object* v_body_3396_; 
v_body_3396_ = lean_ctor_get(v_a_3394_, 2);
if (lean_obj_tag(v_body_3396_) == 3)
{
lean_object* v_u_3397_; lean_object* v_u_3398_; lean_object* v___x_3399_; 
lean_inc_ref(v_body_3396_);
lean_inc_ref(v_binderType_3395_);
lean_dec_ref_known(v_a_3394_, 3);
v_u_3397_ = lean_ctor_get(v_binderType_3395_, 0);
lean_inc(v_u_3397_);
lean_dec_ref_known(v_binderType_3395_, 1);
v_u_3398_ = lean_ctor_get(v_body_3396_, 0);
lean_inc(v_u_3398_);
lean_dec_ref_known(v_body_3396_, 1);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
lean_inc(v_fst_3357_);
v___x_3399_ = lean_infer_type(v_fst_3357_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
v___x_3401_ = lean_whnf(v_a_3400_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
if (lean_obj_tag(v_a_3402_) == 7)
{
lean_object* v_binderType_3403_; 
v_binderType_3403_ = lean_ctor_get(v_a_3402_, 1);
if (lean_obj_tag(v_binderType_3403_) == 3)
{
lean_object* v_body_3404_; 
v_body_3404_ = lean_ctor_get(v_a_3402_, 2);
if (lean_obj_tag(v_body_3404_) == 3)
{
lean_object* v_u_3405_; lean_object* v_u_3406_; lean_object* v___x_3407_; 
lean_inc_ref(v_body_3404_);
lean_inc_ref(v_binderType_3403_);
lean_dec_ref_known(v_a_3402_, 3);
v_u_3405_ = lean_ctor_get(v_binderType_3403_, 0);
lean_inc(v_u_3405_);
lean_dec_ref_known(v_binderType_3403_, 1);
v_u_3406_ = lean_ctor_get(v_body_3404_, 0);
lean_inc(v_u_3406_);
lean_dec_ref_known(v_body_3404_, 1);
v___x_3407_ = l_Lean_Meta_decLevel(v_u_3397_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___x_3409_ = l_Lean_Meta_decLevel(v_u_3405_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
lean_inc(v_a_3408_);
v___x_3411_ = l_Lean_Meta_isLevelDefEq(v_a_3408_, v_a_3410_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3576_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3576_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3576_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_unbox(v_a_3412_);
lean_dec(v_a_3412_);
if (v___x_3416_ == 1)
{
lean_object* v___x_3417_; 
lean_del_object(v___x_3414_);
v___x_3417_ = l_Lean_Meta_decLevel(v_u_3398_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = l_Lean_Meta_decLevel(v_u_3406_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3422_ = lean_box(0);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 1);
lean_ctor_set(v___x_3374_, 1, v___x_3422_);
lean_ctor_set(v___x_3374_, 0, v_a_3420_);
v___x_3424_ = v___x_3374_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3420_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
lean_ctor_set(v___x_3360_, 1, v___x_3424_);
lean_ctor_set(v___x_3360_, 0, v_a_3418_);
v___x_3426_ = v___x_3360_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3418_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3408_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_Expr_const___override(v___x_3421_, v___x_3427_);
v___x_3429_ = lean_unsigned_to_nat(2u);
v___x_3430_ = lean_mk_empty_array_with_capacity(v___x_3429_);
lean_inc(v_fst_3371_);
v___x_3431_ = lean_array_push(v___x_3430_, v_fst_3371_);
lean_inc(v_fst_3357_);
v___x_3432_ = lean_array_push(v___x_3431_, v_fst_3357_);
v___x_3433_ = l_Lean_mkAppN(v___x_3428_, v___x_3432_);
lean_dec_ref(v___x_3432_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_Lean_Meta_trySynthInstance(v___x_3433_, v___x_3434_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3566_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3566_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3566_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_a_3436_) == 1)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; 
lean_del_object(v___x_3438_);
v_a_3440_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v_a_3436_, 1);
lean_inc(v_snd_3372_);
v___x_3441_ = l_Lean_Meta_getDecLevel(v_snd_3372_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
v___x_3443_ = l_Lean_Meta_getDecLevel(v_a_3344_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
lean_inc(v_a_3337_);
v___x_3445_ = l_Lean_Meta_getDecLevel(v_a_3337_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___x_3447_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_a_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3422_);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3444_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_a_3442_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
lean_inc_ref(v___x_3450_);
v___x_3451_ = l_Lean_mkConst(v___x_3447_, v___x_3450_);
v___x_3452_ = lean_unsigned_to_nat(5u);
v___x_3453_ = lean_mk_empty_array_with_capacity(v___x_3452_);
lean_inc(v_fst_3371_);
v___x_3454_ = lean_array_push(v___x_3453_, v_fst_3371_);
lean_inc(v_fst_3357_);
v___x_3455_ = lean_array_push(v___x_3454_, v_fst_3357_);
lean_inc(v_a_3440_);
v___x_3456_ = lean_array_push(v___x_3455_, v_a_3440_);
lean_inc(v_snd_3372_);
v___x_3457_ = lean_array_push(v___x_3456_, v_snd_3372_);
lean_inc_ref(v_e_3308_);
v___x_3458_ = lean_array_push(v___x_3457_, v_e_3308_);
v___x_3459_ = l_Lean_mkAppN(v___x_3451_, v___x_3458_);
lean_dec_ref(v___x_3458_);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
lean_inc_ref(v___x_3459_);
v___x_3460_ = lean_infer_type(v___x_3459_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
lean_inc(v_a_3337_);
v___x_3462_ = l_Lean_Meta_isExprDefEq(v_a_3337_, v_a_3461_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3557_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3557_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3557_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_unbox(v_a_3463_);
lean_dec(v_a_3463_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
lean_del_object(v___x_3465_);
lean_dec_ref(v___x_3459_);
lean_del_object(v___x_3369_);
lean_inc(v_fst_3357_);
v___x_3468_ = l_Lean_Meta_isMonad_x3f(v_fst_3357_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3549_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3549_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3549_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 1)
{
lean_object* v_val_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3545_; 
lean_del_object(v___x_3471_);
v_val_3473_ = lean_ctor_get(v_a_3469_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_a_3469_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3475_ = v_a_3469_;
v_isShared_3476_ = v_isSharedCheck_3545_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_val_3473_);
lean_dec(v_a_3469_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3545_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; 
lean_inc(v_snd_3372_);
v___x_3477_ = l_Lean_Meta_getLevel(v_snd_3372_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
lean_inc(v_snd_3358_);
v___x_3479_ = l_Lean_Meta_getLevel(v_snd_3358_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3482_ = 0;
v___x_3483_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3480_);
lean_ctor_set(v___x_3484_, 1, v___x_3422_);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_a_3478_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = l_Lean_mkConst(v___x_3483_, v___x_3485_);
v___x_3487_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3488_ = lean_unsigned_to_nat(3u);
v___x_3489_ = lean_mk_empty_array_with_capacity(v___x_3488_);
lean_inc_n(v_snd_3372_, 2);
v___x_3490_ = lean_array_push(v___x_3489_, v_snd_3372_);
v___x_3491_ = lean_array_push(v___x_3490_, v___x_3487_);
lean_inc(v_snd_3358_);
v___x_3492_ = lean_array_push(v___x_3491_, v_snd_3358_);
v___x_3493_ = l_Lean_mkAppN(v___x_3486_, v___x_3492_);
lean_dec_ref(v___x_3492_);
v___x_3494_ = l_Lean_mkForall(v___x_3481_, v___x_3482_, v_snd_3372_, v___x_3493_);
v___x_3495_ = l_Lean_Meta_trySynthInstance(v___x_3494_, v___x_3434_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3541_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3541_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3541_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_del_object(v___x_3498_);
v_a_3500_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v_a_3496_, 1);
v___x_3501_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3502_ = l_Lean_mkConst(v___x_3501_, v___x_3450_);
v___x_3503_ = lean_unsigned_to_nat(8u);
v___x_3504_ = lean_mk_empty_array_with_capacity(v___x_3503_);
v___x_3505_ = lean_array_push(v___x_3504_, v_fst_3371_);
v___x_3506_ = lean_array_push(v___x_3505_, v_fst_3357_);
v___x_3507_ = lean_array_push(v___x_3506_, v_snd_3372_);
v___x_3508_ = lean_array_push(v___x_3507_, v_snd_3358_);
v___x_3509_ = lean_array_push(v___x_3508_, v_a_3440_);
v___x_3510_ = lean_array_push(v___x_3509_, v_a_3500_);
v___x_3511_ = lean_array_push(v___x_3510_, v_val_3473_);
v___x_3512_ = lean_array_push(v___x_3511_, v_e_3308_);
v___x_3513_ = l_Lean_mkAppN(v___x_3502_, v___x_3512_);
lean_dec_ref(v___x_3512_);
v___x_3514_ = l_Lean_Meta_expandCoe(v___x_3513_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v_fst_3516_; lean_object* v___x_3517_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v_fst_3516_ = lean_ctor_get(v_a_3515_, 0);
lean_inc_n(v_fst_3516_, 2);
lean_dec(v_a_3515_);
lean_inc(v_a_3313_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc_ref(v_a_3310_);
v___x_3517_ = lean_infer_type(v_fst_3516_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = l_Lean_Meta_isExprDefEq(v_a_3337_, v_a_3518_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3534_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3534_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3534_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_unbox(v_a_3520_);
lean_dec(v_a_3520_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_fst_3516_);
lean_del_object(v___x_3475_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3434_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3434_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
else
{
lean_object* v___x_3529_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v_fst_3516_);
v___x_3529_ = v___x_3475_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_fst_3516_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3529_);
v___x_3531_ = v___x_3522_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
else
{
lean_object* v_a_3535_; 
lean_dec(v_fst_3516_);
lean_del_object(v___x_3475_);
v_a_3535_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3519_, 1);
v_a_3322_ = v_a_3535_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3536_; 
lean_dec(v_fst_3516_);
lean_del_object(v___x_3475_);
lean_dec(v_a_3337_);
v_a_3536_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3517_, 1);
v_a_3322_ = v_a_3536_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3537_; 
lean_del_object(v___x_3475_);
lean_dec(v_a_3337_);
v_a_3537_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3514_, 1);
v_a_3322_ = v_a_3537_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3539_; 
lean_dec(v_a_3496_);
lean_del_object(v___x_3475_);
lean_dec(v_val_3473_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3434_);
v___x_3539_ = v___x_3498_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3434_);
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
lean_object* v_a_3542_; 
lean_del_object(v___x_3475_);
lean_dec(v_val_3473_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3542_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3495_, 1);
v_a_3322_ = v_a_3542_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3543_; 
lean_dec(v_a_3478_);
lean_del_object(v___x_3475_);
lean_dec(v_val_3473_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3543_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3479_, 1);
v_a_3322_ = v_a_3543_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3544_; 
lean_del_object(v___x_3475_);
lean_dec(v_val_3473_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3544_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3477_, 1);
v_a_3322_ = v_a_3544_;
goto v___jp_3321_;
}
}
}
else
{
lean_object* v___x_3547_; 
lean_dec(v_a_3469_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3434_);
v___x_3547_ = v___x_3471_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3434_);
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
else
{
lean_object* v_a_3550_; 
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3550_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3468_, 1);
v_a_3322_ = v_a_3550_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3459_);
v___x_3552_ = v___x_3369_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3459_);
v___x_3552_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3552_);
v___x_3554_ = v___x_3465_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_object* v_a_3558_; 
lean_dec_ref(v___x_3459_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3558_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3462_, 1);
v_a_3322_ = v_a_3558_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3559_; 
lean_dec_ref(v___x_3459_);
lean_dec_ref_known(v___x_3450_, 2);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3559_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3460_, 1);
v_a_3322_ = v_a_3559_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3560_; 
lean_dec(v_a_3444_);
lean_dec(v_a_3442_);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3560_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3445_, 1);
v_a_3322_ = v_a_3560_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3561_; 
lean_dec(v_a_3442_);
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3561_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3443_, 1);
v_a_3322_ = v_a_3561_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3562_; 
lean_dec(v_a_3440_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3562_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3441_, 1);
v_a_3322_ = v_a_3562_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3564_; 
lean_dec(v_a_3436_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3434_);
v___x_3564_ = v___x_3438_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3434_);
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
lean_object* v_a_3567_; 
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3567_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3435_, 1);
v_a_3322_ = v_a_3567_;
goto v___jp_3321_;
}
}
}
}
else
{
lean_object* v_a_3570_; 
lean_dec(v_a_3418_);
lean_dec(v_a_3408_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3570_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3419_, 1);
v_a_3322_ = v_a_3570_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3571_; 
lean_dec(v_a_3408_);
lean_dec(v_u_3406_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3571_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3417_, 1);
v_a_3322_ = v_a_3571_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
lean_dec(v_a_3408_);
lean_dec(v_u_3406_);
lean_dec(v_u_3398_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3572_ = lean_box(0);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3572_);
v___x_3574_ = v___x_3414_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; 
lean_dec(v_a_3408_);
lean_dec(v_u_3406_);
lean_dec(v_u_3398_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3577_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3411_, 1);
v_a_3322_ = v_a_3577_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3578_; 
lean_dec(v_a_3408_);
lean_dec(v_u_3406_);
lean_dec(v_u_3398_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3578_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3409_, 1);
v_a_3322_ = v_a_3578_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3579_; 
lean_dec(v_u_3406_);
lean_dec(v_u_3405_);
lean_dec(v_u_3398_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3579_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3407_, 1);
v_a_3322_ = v_a_3579_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3580_; 
lean_dec(v_u_3398_);
lean_dec(v_u_3397_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3580_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3402_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec_ref_known(v_a_3402_, 3);
v___y_3326_ = v___x_3580_;
goto v___jp_3325_;
}
}
else
{
lean_object* v___x_3581_; 
lean_dec(v_u_3398_);
lean_dec(v_u_3397_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3581_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3402_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec_ref_known(v_a_3402_, 3);
v___y_3326_ = v___x_3581_;
goto v___jp_3325_;
}
}
else
{
lean_object* v___x_3582_; 
lean_dec(v_u_3398_);
lean_dec(v_u_3397_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3582_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3402_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3402_);
v___y_3326_ = v___x_3582_;
goto v___jp_3325_;
}
}
else
{
lean_object* v_a_3583_; 
lean_dec(v_u_3398_);
lean_dec(v_u_3397_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3583_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3401_, 1);
v_a_3322_ = v_a_3583_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3584_; 
lean_dec(v_u_3398_);
lean_dec(v_u_3397_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3584_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3399_, 1);
v_a_3322_ = v_a_3584_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3585_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3585_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3394_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec_ref_known(v_a_3394_, 3);
v___y_3326_ = v___x_3585_;
goto v___jp_3325_;
}
}
else
{
lean_object* v___x_3586_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3586_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3394_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec_ref_known(v_a_3394_, 3);
v___y_3326_ = v___x_3586_;
goto v___jp_3325_;
}
}
else
{
lean_object* v___x_3587_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3587_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3394_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3394_);
v___y_3326_ = v___x_3587_;
goto v___jp_3325_;
}
}
else
{
lean_object* v_a_3588_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3588_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3393_, 1);
v_a_3322_ = v_a_3588_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3589_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3589_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3391_, 1);
v_a_3322_ = v_a_3589_;
goto v___jp_3321_;
}
}
}
else
{
lean_object* v___x_3590_; 
lean_del_object(v___x_3381_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3360_);
lean_dec(v_a_3344_);
lean_dec(v_a_3337_);
v___x_3590_ = l_Lean_Meta_isMonad_x3f(v_fst_3357_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3683_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3683_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3683_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
if (lean_obj_tag(v_a_3591_) == 1)
{
lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3595_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_fst_3371_);
v___x_3597_ = v___x_3369_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_fst_3371_);
v___x_3597_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3599_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_snd_3372_);
v___x_3599_ = v___x_3355_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_snd_3372_);
v___x_3599_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 1);
lean_ctor_set(v___x_3346_, 0, v_snd_3358_);
v___x_3601_ = v___x_3346_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_snd_3358_);
v___x_3601_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___y_3604_; uint8_t v___y_3605_; lean_object* v_a_3627_; lean_object* v___x_3631_; 
v___x_3602_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set_tag(v___x_3339_, 1);
lean_ctor_set(v___x_3339_, 0, v_e_3308_);
v___x_3631_ = v___x_3339_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_e_3308_);
v___x_3631_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3630_;
}
v___jp_3603_:
{
if (v___y_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec_ref(v___y_3604_);
lean_del_object(v___x_3593_);
v___x_3606_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3377_, v_a_3311_, v_a_3313_);
lean_dec(v_a_3377_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3606_, 0);
lean_dec(v_unused_3614_);
v___x_3608_ = v___x_3606_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_dec(v___x_3606_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3602_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3602_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v_a_3615_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3606_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3606_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v___x_3624_; 
lean_dec(v_a_3377_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 1);
lean_ctor_set(v___x_3593_, 0, v___y_3604_);
v___x_3624_ = v___x_3593_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___y_3604_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
v___jp_3626_:
{
uint8_t v___x_3628_; 
v___x_3628_ = l_Lean_Exception_isInterrupt(v_a_3627_);
if (v___x_3628_ == 0)
{
uint8_t v___x_3629_; 
lean_inc_ref(v_a_3627_);
v___x_3629_ = l_Lean_Exception_isRuntime(v_a_3627_);
v___y_3604_ = v_a_3627_;
v___y_3605_ = v___x_3629_;
goto v___jp_3603_;
}
else
{
v___y_3604_ = v_a_3627_;
v___y_3605_ = v___x_3628_;
goto v___jp_3603_;
}
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3632_ = lean_unsigned_to_nat(6u);
v___x_3633_ = lean_mk_empty_array_with_capacity(v___x_3632_);
v___x_3634_ = lean_array_push(v___x_3633_, v___x_3597_);
v___x_3635_ = lean_array_push(v___x_3634_, v___x_3599_);
v___x_3636_ = lean_array_push(v___x_3635_, v___x_3601_);
v___x_3637_ = lean_array_push(v___x_3636_, v___x_3602_);
v___x_3638_ = lean_array_push(v___x_3637_, v_a_3591_);
v___x_3639_ = lean_array_push(v___x_3638_, v___x_3631_);
v___x_3640_ = l_Lean_Meta_mkAppOptM(v___x_3595_, v___x_3639_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3659_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3643_ = v___x_3640_;
v_isShared_3644_ = v_isSharedCheck_3659_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3659_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_Meta_expandCoe(v_a_3641_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3657_; 
lean_del_object(v___x_3593_);
lean_dec(v_a_3377_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3657_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3657_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_fst_3650_; lean_object* v___x_3652_; 
v_fst_3650_ = lean_ctor_get(v_a_3646_, 0);
lean_inc(v_fst_3650_);
lean_dec(v_a_3646_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 1);
lean_ctor_set(v___x_3643_, 0, v_fst_3650_);
v___x_3652_ = v___x_3643_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_fst_3650_);
v___x_3652_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3652_);
v___x_3654_ = v___x_3648_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3658_; 
lean_del_object(v___x_3643_);
v_a_3658_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3645_, 1);
v_a_3627_ = v_a_3658_;
goto v___jp_3626_;
}
}
}
else
{
lean_object* v_a_3660_; 
v_a_3660_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3640_, 1);
v_a_3627_ = v_a_3660_;
goto v___jp_3626_;
}
}
}
}
}
}
else
{
lean_object* v___x_3665_; 
lean_del_object(v___x_3593_);
lean_dec(v_a_3591_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_del_object(v___x_3339_);
lean_dec_ref(v_e_3308_);
v___x_3665_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3377_, v_a_3311_, v_a_3313_);
lean_dec(v_a_3377_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3673_; 
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___x_3665_, 0);
lean_dec(v_unused_3674_);
v___x_3667_ = v___x_3665_;
v_isShared_3668_ = v_isSharedCheck_3673_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v___x_3665_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3673_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3669_ = lean_box(0);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3669_);
v___x_3671_ = v___x_3667_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
v_a_3675_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3665_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3665_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3377_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_dec(v_snd_3358_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_del_object(v___x_3339_);
lean_dec_ref(v_e_3308_);
return v___x_3590_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3377_);
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3685_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3378_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3378_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_del_object(v___x_3374_);
lean_dec(v_snd_3372_);
lean_dec(v_fst_3371_);
lean_del_object(v___x_3369_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3693_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3376_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3376_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
lean_dec(v_a_3363_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3703_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3703_);
v___x_3705_ = v___x_3365_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3708_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3362_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3362_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec(v_a_3349_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v___x_3718_ = lean_box(0);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3718_);
v___x_3720_ = v___x_3351_;
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
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3346_);
lean_dec(v_a_3344_);
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3723_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3348_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3348_);
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
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_del_object(v___x_3339_);
lean_dec(v_a_3337_);
lean_dec_ref(v_e_3308_);
v_a_3732_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3341_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3341_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3741_, lean_object* v_expectedType_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3741_, v_expectedType_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3749_, lean_object* v_expectedType_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; 
lean_inc_ref(v_expectedType_3750_);
lean_inc_ref(v_expr_3749_);
v___x_3756_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3749_, v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3836_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3836_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3836_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
if (lean_obj_tag(v_a_3757_) == 1)
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_val_3761_ = lean_ctor_get(v_a_3757_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_a_3757_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3763_ = v_a_3757_;
v_isShared_3764_ = v_isSharedCheck_3773_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v_a_3757_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3773_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3765_ = lean_box(0);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_val_3761_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3768_);
v___x_3770_ = v___x_3759_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v___x_3774_; 
lean_del_object(v___x_3759_);
lean_dec(v_a_3757_);
lean_inc_ref(v_expectedType_3750_);
v___x_3774_ = l_Lean_Meta_whnfR(v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; uint8_t v___x_3776_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___x_3774_, 1);
v___x_3776_ = l_Lean_Expr_isForall(v_a_3775_);
lean_dec(v_a_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3749_, v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; 
lean_inc_ref(v_expr_3749_);
v___x_3778_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3749_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
if (lean_obj_tag(v_a_3779_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3818_; 
v_val_3780_ = lean_ctor_get(v_a_3779_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3779_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3782_ = v_a_3779_;
v_isShared_3783_ = v_isSharedCheck_3818_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_val_3780_);
lean_dec(v_a_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3818_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; 
lean_inc(v_a_3754_);
lean_inc_ref(v_a_3753_);
lean_inc(v_a_3752_);
lean_inc_ref(v_a_3751_);
lean_inc(v_val_3780_);
v___x_3784_ = lean_infer_type(v_val_3780_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
lean_inc_ref(v_expectedType_3750_);
v___x_3786_ = l_Lean_Meta_isExprDefEq(v_a_3785_, v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3801_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3801_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3801_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_unbox(v_a_3787_);
lean_dec(v_a_3787_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_del_object(v___x_3789_);
lean_del_object(v___x_3782_);
lean_dec(v_val_3780_);
v___x_3792_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3749_, v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v_val_3780_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3794_);
v___x_3796_ = v___x_3782_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3796_);
v___x_3798_ = v___x_3789_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_del_object(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_a_3802_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3786_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3786_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_del_object(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_a_3810_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3784_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3784_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
else
{
lean_object* v___x_3819_; 
lean_dec(v_a_3779_);
v___x_3819_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3749_, v_expectedType_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
return v___x_3819_;
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_a_3820_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3778_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3778_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_a_3828_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3774_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3774_);
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
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_expectedType_3750_);
lean_dec_ref(v_expr_3749_);
v_a_3837_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3756_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3756_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3845_, lean_object* v_expectedType_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3845_, v_expectedType_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3853_, lean_object* v_expectedType_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3853_, v_expectedType_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3885_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3885_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3885_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
switch(lean_obj_tag(v_a_3861_))
{
case 0:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_box(0);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
case 1:
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3880_; 
v_a_3869_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3871_ = v_a_3861_;
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v_a_3861_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v_fst_3873_; lean_object* v___x_3875_; 
v_fst_3873_ = lean_ctor_get(v_a_3869_, 0);
lean_inc(v_fst_3873_);
lean_dec(v_a_3869_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v_fst_3873_);
v___x_3875_ = v___x_3871_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_fst_3873_);
v___x_3875_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3877_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3875_);
v___x_3877_ = v___x_3863_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
default: 
{
lean_object* v___x_3881_; lean_object* v___x_3883_; 
v___x_3881_ = lean_box(2);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3881_);
v___x_3883_ = v___x_3863_;
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
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v_a_3886_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3860_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3860_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3894_, lean_object* v_expectedType_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_Meta_coerce_x3f(v_expr_3894_, v_expectedType_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
return v_res_3901_;
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
