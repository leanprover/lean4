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
lean_object* v___x_232_; lean_object* v___x_233_; double v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_box(0);
v___x_234_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
v___x_235_ = 0;
v___x_236_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_237_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_237_, 0, v_cls_200_);
lean_ctor_set(v___x_237_, 1, v___x_233_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_ctor_set_float(v___x_237_, sizeof(void*)*3, v___x_234_);
lean_ctor_set_float(v___x_237_, sizeof(void*)*3 + 8, v___x_234_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*3 + 16, v___x_235_);
v___x_238_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_239_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v_a_210_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
lean_inc(v_ref_208_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_ref_208_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Lean_PersistentArray_push___redArg(v_traces_228_, v___x_240_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_241_);
v___x_243_ = v___x_230_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_241_);
lean_ctor_set_uint64(v_reuseFailAlloc_252_, sizeof(void*)*1, v_tid_227_);
v___x_243_ = v_reuseFailAlloc_252_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 4, v___x_243_);
v___x_245_ = v___x_225_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_env_216_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_251_, 5, v_cache_220_);
lean_ctor_set(v_reuseFailAlloc_251_, 6, v_messages_221_);
lean_ctor_set(v_reuseFailAlloc_251_, 7, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_251_, 8, v_snapshotTasks_223_);
v___x_245_ = v_reuseFailAlloc_251_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_246_ = lean_st_ref_put(v___y_206_, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_232_);
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
size_t v_x_36082__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_x_36082__boxed_302_ = lean_unbox_usize(v_x_300_);
lean_dec(v_x_300_);
v_res_303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_299_, v_x_36082__boxed_302_, v_x_301_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_315_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
v___x_321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_ctor_set(v___x_321_, 3, v___x_320_);
lean_ctor_set(v___x_321_, 4, v___x_320_);
lean_ctor_set(v___x_321_, 5, v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_cls_336_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_337_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13));
v___x_338_ = l_Lean_Name_append(v___x_337_, v_cls_336_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_349_, uint8_t v_isMeta_350_, lean_object* v_hint_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_env_360_; uint8_t v_isExporting_361_; lean_object* v_entry_362_; lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_358_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0);
v___x_359_ = lean_st_ref_get(v___y_356_);
v_env_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_env_360_);
lean_dec(v___x_359_);
v_isExporting_361_ = lean_ctor_get_uint8(v_env_360_, sizeof(void*)*8);
lean_dec_ref(v_env_360_);
lean_inc(v_mod_349_);
v_entry_362_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_362_, 0, v_mod_349_);
lean_ctor_set_uint8(v_entry_362_, sizeof(void*)*1, v_isExporting_361_);
lean_ctor_set_uint8(v_entry_362_, sizeof(void*)*1 + 1, v_isMeta_350_);
v___x_363_ = lean_st_ref_get(v___y_356_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_366_ = lean_box(1);
v___x_367_ = lean_box(0);
v___x_412_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_358_, v___x_365_, v_env_364_, v___x_366_, v___x_367_);
v___x_413_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_412_, v_entry_362_);
lean_dec(v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v_toCold_414_; lean_object* v_options_415_; uint8_t v_hasTrace_416_; 
v_toCold_414_ = lean_ctor_get(v___y_355_, 0);
v_options_415_ = lean_ctor_get(v_toCold_414_, 2);
v_hasTrace_416_ = lean_ctor_get_uint8(v_options_415_, sizeof(void*)*1);
if (v_hasTrace_416_ == 0)
{
lean_dec(v_hint_351_);
lean_dec(v_mod_349_);
v___y_369_ = v___y_352_;
v___y_370_ = v___y_354_;
v___y_371_ = v___y_356_;
goto v___jp_368_;
}
else
{
lean_object* v_inheritedTraceOptions_417_; lean_object* v_cls_418_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_inheritedTraceOptions_417_ = lean_ctor_get(v_toCold_414_, 11);
v_cls_418_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6));
v___x_440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14);
v___x_441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_417_, v_options_415_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec(v_hint_351_);
lean_dec(v_mod_349_);
v___y_369_ = v___y_352_;
v___y_370_ = v___y_354_;
v___y_371_ = v___y_356_;
goto v___jp_368_;
}
else
{
lean_object* v___x_442_; lean_object* v___y_444_; 
v___x_442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
if (v_isExporting_361_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_444_ = v___x_451_;
goto v___jp_443_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_444_ = v___x_452_;
goto v___jp_443_;
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_inc_ref(v___y_444_);
v___x_445_ = l_Lean_stringToMessageData(v___y_444_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_442_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
if (v_isMeta_350_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_427_ = v___x_448_;
v___y_428_ = v___x_449_;
goto v___jp_426_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
v___y_427_ = v___x_448_;
v___y_428_ = v___x_450_;
goto v___jp_426_;
}
}
}
v___jp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___y_420_);
lean_ctor_set(v___x_422_, 1, v___y_421_);
v___x_423_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_418_, v___x_422_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_snd_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v_snd_425_ = lean_ctor_get(v_a_424_, 1);
lean_inc(v_snd_425_);
lean_dec(v_a_424_);
v___y_369_ = v_snd_425_;
v___y_370_ = v___y_354_;
v___y_371_ = v___y_356_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_entry_362_, 1);
return v___x_423_;
}
}
v___jp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
lean_inc_ref(v___y_428_);
v___x_429_ = l_Lean_stringToMessageData(v___y_428_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___y_427_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_MessageData_ofName(v_mod_349_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_Name_isAnonymous(v_hint_351_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_437_ = l_Lean_MessageData_ofName(v_hint_351_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___y_420_ = v___x_434_;
v___y_421_ = v___x_438_;
goto v___jp_419_;
}
else
{
lean_object* v___x_439_; 
lean_dec(v_hint_351_);
v___x_439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11);
v___y_420_ = v___x_434_;
v___y_421_ = v___x_439_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref_known(v_entry_362_, 1);
lean_dec(v_hint_351_);
lean_dec(v_mod_349_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___y_352_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
v___jp_368_:
{
lean_object* v___x_372_; lean_object* v_toEnvExtension_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_traceState_378_; lean_object* v_messages_379_; lean_object* v_infoState_380_; lean_object* v_snapshotTasks_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_410_; 
v___x_372_ = lean_st_ref_take(v___y_371_);
v_toEnvExtension_373_ = lean_ctor_get(v___x_365_, 0);
v_env_374_ = lean_ctor_get(v___x_372_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_372_, 1);
v_ngen_376_ = lean_ctor_get(v___x_372_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_372_, 3);
v_traceState_378_ = lean_ctor_get(v___x_372_, 4);
v_messages_379_ = lean_ctor_get(v___x_372_, 6);
v_infoState_380_ = lean_ctor_get(v___x_372_, 7);
v_snapshotTasks_381_ = lean_ctor_get(v___x_372_, 8);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_372_, 5);
lean_dec(v_unused_411_);
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_410_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snapshotTasks_381_);
lean_inc(v_infoState_380_);
lean_inc(v_messages_379_);
lean_inc(v_traceState_378_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_410_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_asyncMode_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v_asyncMode_385_ = lean_ctor_get(v_toEnvExtension_373_, 2);
v___x_386_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_365_, v_env_374_, v_entry_362_, v_asyncMode_385_, v___x_367_);
v___x_387_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 5, v___x_387_);
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_378_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_messages_379_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_infoState_380_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_snapshotTasks_381_);
v___x_389_ = v_reuseFailAlloc_409_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_mctx_392_; lean_object* v_zetaDeltaFVarIds_393_; lean_object* v_postponed_394_; lean_object* v_diag_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_407_; 
v___x_390_ = lean_st_ref_put(v___y_371_, v___x_389_);
v___x_391_ = lean_st_ref_take(v___y_370_);
v_mctx_392_ = lean_ctor_get(v___x_391_, 0);
v_zetaDeltaFVarIds_393_ = lean_ctor_get(v___x_391_, 2);
v_postponed_394_ = lean_ctor_get(v___x_391_, 3);
v_diag_395_ = lean_ctor_get(v___x_391_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_408_);
v___x_397_ = v___x_391_;
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_diag_395_);
lean_inc(v_postponed_394_);
lean_inc(v_zetaDeltaFVarIds_393_);
lean_inc(v_mctx_392_);
lean_dec(v___x_391_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
v___x_400_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_mctx_392_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_393_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_394_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_395_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_st_ref_put(v___y_370_, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_399_);
lean_ctor_set(v___x_404_, 1, v___y_369_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_456_, lean_object* v_isMeta_457_, lean_object* v_hint_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_isMeta_boxed_465_; lean_object* v_res_466_; 
v_isMeta_boxed_465_ = lean_unbox(v_isMeta_457_);
v_res_466_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_456_, v_isMeta_boxed_465_, v_hint_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(0);
return v___x_469_;
}
else
{
lean_object* v_key_470_; lean_object* v_value_471_; lean_object* v_tail_472_; uint8_t v___x_473_; 
v_key_470_ = lean_ctor_get(v_x_468_, 0);
v_value_471_ = lean_ctor_get(v_x_468_, 1);
v_tail_472_ = lean_ctor_get(v_x_468_, 2);
v___x_473_ = lean_name_eq(v_key_470_, v_a_467_);
if (v___x_473_ == 0)
{
v_x_468_ = v_tail_472_;
goto _start;
}
else
{
lean_object* v___x_475_; 
lean_inc(v_value_471_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_value_471_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_476_, v_x_477_);
lean_dec(v_x_477_);
lean_dec(v_a_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_buckets_481_; lean_object* v___x_482_; uint64_t v___y_484_; 
v_buckets_481_ = lean_ctor_get(v_m_479_, 1);
v___x_482_ = lean_array_get_size(v_buckets_481_);
if (lean_obj_tag(v_a_480_) == 0)
{
uint64_t v___x_498_; 
v___x_498_ = 1723ULL;
v___y_484_ = v___x_498_;
goto v___jp_483_;
}
else
{
uint64_t v_hash_499_; 
v_hash_499_ = lean_ctor_get_uint64(v_a_480_, sizeof(void*)*2);
v___y_484_ = v_hash_499_;
goto v___jp_483_;
}
v___jp_483_:
{
uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v_fold_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_485_ = 32ULL;
v___x_486_ = lean_uint64_shift_right(v___y_484_, v___x_485_);
v_fold_487_ = lean_uint64_xor(v___y_484_, v___x_486_);
v___x_488_ = 16ULL;
v___x_489_ = lean_uint64_shift_right(v_fold_487_, v___x_488_);
v___x_490_ = lean_uint64_xor(v_fold_487_, v___x_489_);
v___x_491_ = lean_uint64_to_usize(v___x_490_);
v___x_492_ = lean_usize_of_nat(v___x_482_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_sub(v___x_492_, v___x_493_);
v___x_495_ = lean_usize_land(v___x_491_, v___x_494_);
v___x_496_ = lean_array_uget_borrowed(v_buckets_481_, v___x_495_);
v___x_497_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_480_, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_m_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_503_, lean_object* v_declName_504_, lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_declName_504_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_b_508_);
lean_ctor_set(v___x_516_, 1, v___y_509_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v_modules_519_; lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v_toImport_523_; lean_object* v_module_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; 
v___x_518_ = l_Lean_Environment_header(v___x_503_);
v_modules_519_ = lean_ctor_get(v___x_518_, 3);
lean_inc_ref(v_modules_519_);
lean_dec_ref(v___x_518_);
v___x_520_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_521_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
v___x_522_ = lean_array_get(v___x_520_, v_modules_519_, v_a_521_);
lean_dec_ref(v_modules_519_);
v_toImport_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc_ref(v_toImport_523_);
lean_dec(v___x_522_);
v_module_524_ = lean_ctor_get(v_toImport_523_, 0);
lean_inc(v_module_524_);
lean_dec_ref(v_toImport_523_);
v___x_525_ = lean_box(0);
v___x_526_ = 0;
lean_inc(v_declName_504_);
v___x_527_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_524_, v___x_526_, v_declName_504_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v_snd_529_; size_t v___x_530_; size_t v___x_531_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v_snd_529_ = lean_ctor_get(v_a_528_, 1);
lean_inc(v_snd_529_);
lean_dec(v_a_528_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_507_, v___x_530_);
v_i_507_ = v___x_531_;
v_b_508_ = v___x_525_;
v___y_509_ = v_snd_529_;
goto _start;
}
else
{
lean_dec(v_declName_504_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_533_, lean_object* v_declName_534_, lean_object* v_as_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v_i_boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_546_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_533_, v_declName_534_, v_as_535_, v_sz_boxed_545_, v_i_boxed_546_, v_b_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec_ref(v_as_535_);
lean_dec_ref(v___x_533_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0(void){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_HashMap_instInhabited___redArg();
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_551_, uint8_t v_isMeta_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_env_565_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___x_590_; 
v___x_559_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0);
v___x_560_ = lean_st_ref_get(v___y_557_);
v_env_565_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_env_565_);
lean_dec(v___x_560_);
v___x_590_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_565_, v_declName_551_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_dec_ref(v_env_565_);
lean_dec(v_declName_551_);
goto v___jp_561_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_592_; lean_object* v_modules_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_val_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Lean_Environment_header(v_env_565_);
v_modules_593_ = lean_ctor_get(v___x_592_, 3);
lean_inc_ref(v_modules_593_);
lean_dec_ref(v___x_592_);
v___x_594_ = lean_array_get_size(v_modules_593_);
v___x_595_ = lean_nat_dec_lt(v_val_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_modules_593_);
lean_dec(v_val_591_);
lean_dec_ref(v_env_565_);
lean_dec(v_declName_551_);
goto v___jp_561_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___y_599_; 
v___x_596_ = lean_array_fget(v_modules_593_, v_val_591_);
lean_dec(v_val_591_);
lean_dec_ref(v_modules_593_);
v___x_597_ = lean_st_ref_get(v___y_557_);
if (v_isMeta_552_ == 0)
{
lean_dec(v___x_597_);
v___y_599_ = v_isMeta_552_;
goto v___jp_598_;
}
else
{
lean_object* v_env_612_; uint8_t v___x_613_; 
v_env_612_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_612_);
lean_dec(v___x_597_);
lean_inc(v_declName_551_);
v___x_613_ = l_Lean_isMarkedMeta(v_env_612_, v_declName_551_);
if (v___x_613_ == 0)
{
v___y_599_ = v_isMeta_552_;
goto v___jp_598_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = 0;
v___y_599_ = v___x_614_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v_toImport_600_; lean_object* v_module_601_; lean_object* v___x_602_; 
v_toImport_600_ = lean_ctor_get(v___x_596_, 0);
lean_inc_ref(v_toImport_600_);
lean_dec(v___x_596_);
v_module_601_ = lean_ctor_get(v_toImport_600_, 0);
lean_inc(v_module_601_);
lean_dec_ref(v_toImport_600_);
lean_inc(v_declName_551_);
v___x_602_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_601_, v___y_599_, v_declName_551_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_snd_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_snd_604_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_604_);
lean_dec(v_a_603_);
v___x_605_ = l_Lean_indirectModUseExt;
v___x_606_ = lean_box(1);
v___x_607_ = lean_box(0);
lean_inc_ref(v_env_565_);
v___x_608_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_559_, v___x_605_, v_env_565_, v___x_606_, v___x_607_);
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_608_, v_declName_551_);
lean_dec(v___x_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___y_567_ = v_snd_604_;
v___y_568_ = v___x_610_;
goto v___jp_566_;
}
else
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_609_, 1);
v___y_567_ = v_snd_604_;
v___y_568_ = v_val_611_;
goto v___jp_566_;
}
}
else
{
lean_dec_ref(v_env_565_);
lean_dec(v_declName_551_);
return v___x_602_;
}
}
}
}
v___jp_561_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___y_553_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
v___jp_566_:
{
lean_object* v___x_569_; size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_box(0);
v_sz_570_ = lean_array_size(v___y_568_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_565_, v_declName_551_, v___y_568_, v_sz_570_, v___x_571_, v___x_569_, v___y_567_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v_env_565_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_589_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_589_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_589_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_589_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
v_snd_577_ = lean_ctor_get(v_a_573_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_a_573_, 0);
lean_dec(v_unused_588_);
v___x_579_ = v_a_573_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_dec(v_a_573_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_569_);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_577_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_582_);
v___x_584_ = v___x_575_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
else
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_615_, lean_object* v_isMeta_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_isMeta_boxed_623_; lean_object* v_res_624_; 
v_isMeta_boxed_623_ = lean_unbox(v_isMeta_616_);
v_res_624_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_615_, v_isMeta_boxed_623_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___y_640_; lean_object* v_f_644_; uint8_t v___x_645_; 
v_f_644_ = l_Lean_Expr_getAppFn(v_e_632_);
v___x_645_ = l_Lean_Expr_isConst(v_f_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_f_644_);
lean_dec_ref(v_e_632_);
v___y_640_ = v___y_633_;
goto v___jp_639_;
}
else
{
lean_object* v_declName_646_; lean_object* v___x_647_; lean_object* v_env_648_; uint8_t v___x_649_; 
v_declName_646_ = l_Lean_Expr_constName_x21(v_f_644_);
lean_dec_ref(v_f_644_);
v___x_647_ = lean_st_ref_get(v___y_637_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
lean_inc(v_declName_646_);
v___x_649_ = l_Lean_Meta_isCoeDecl(v_env_648_, v_declName_646_);
if (v___x_649_ == 0)
{
lean_dec(v_declName_646_);
lean_dec_ref(v_e_632_);
v___y_640_ = v___y_633_;
goto v___jp_639_;
}
else
{
lean_object* v___x_650_; 
lean_inc(v_declName_646_);
lean_inc_ref(v_e_632_);
v___x_650_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_632_, v_declName_646_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; uint8_t v___x_652_; lean_object* v___x_653_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = 0;
v___x_653_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_651_, v___x_652_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_706_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v_snd_655_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_a_654_, 0);
lean_dec(v_unused_707_);
v___x_657_ = v_a_654_;
v_isShared_658_ = v_isSharedCheck_706_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_dec(v_a_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_706_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; 
lean_inc_ref(v_e_632_);
v___x_659_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_632_, v___x_652_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_697_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_697_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_697_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_697_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
if (lean_obj_tag(v_a_660_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_696_; 
v_val_664_ = lean_ctor_get(v_a_660_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_696_ == 0)
{
v___x_666_ = v_a_660_;
v_isShared_667_ = v_isSharedCheck_696_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_val_664_);
lean_dec(v_a_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_696_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___y_669_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_681_ = lean_name_eq(v_declName_646_, v___x_680_);
lean_dec(v_declName_646_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_e_632_);
v___y_669_ = v_snd_655_;
goto v___jp_668_;
}
else
{
lean_object* v_dummy_682_; lean_object* v_nargs_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_dummy_682_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_683_ = l_Lean_Expr_getAppNumArgs(v_e_632_);
lean_inc(v_nargs_683_);
v___x_684_ = lean_mk_array(v_nargs_683_, v_dummy_682_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v_nargs_683_, v___x_685_);
lean_dec(v_nargs_683_);
v___x_687_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_632_, v___x_684_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(2u);
v___x_689_ = lean_array_get_size(v___x_687_);
v___x_690_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec_ref(v___x_687_);
v___y_669_ = v_snd_655_;
goto v___jp_668_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_array_fget(v___x_687_, v___x_688_);
lean_dec_ref(v___x_687_);
v___x_692_ = l_Lean_Expr_getAppFn(v___x_691_);
lean_dec(v___x_691_);
v___x_693_ = l_Lean_Expr_isConst(v___x_692_);
if (v___x_693_ == 0)
{
lean_dec_ref(v___x_692_);
v___y_669_ = v_snd_655_;
goto v___jp_668_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Lean_Expr_constName_x21(v___x_692_);
lean_dec_ref(v___x_692_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_snd_655_);
v___y_669_ = v___x_695_;
goto v___jp_668_;
}
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_Expr_headBeta(v_val_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_679_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___y_669_);
lean_ctor_set(v___x_657_, 0, v___x_672_);
v___x_674_ = v___x_657_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___y_669_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_674_);
v___x_676_ = v___x_662_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_662_);
lean_dec(v_a_660_);
lean_del_object(v___x_657_);
lean_dec(v_declName_646_);
lean_dec_ref(v_e_632_);
v___y_640_ = v_snd_655_;
goto v___jp_639_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_del_object(v___x_657_);
lean_dec(v_snd_655_);
lean_dec(v_declName_646_);
lean_dec_ref(v_e_632_);
v_a_698_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_659_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_659_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_declName_646_);
lean_dec_ref(v_e_632_);
v_a_708_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_653_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_653_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_declName_646_);
lean_dec(v___y_633_);
lean_dec_ref(v_e_632_);
v_a_716_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_650_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_650_);
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
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___y_640_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_expandCoe___lam__1(v_e_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_733_);
v___x_741_ = lean_apply_8(v_k_732_, v_b_735_, v___y_733_, v___y_734_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, lean_box(0));
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_742_, v___y_743_, v___y_744_, v_b_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_743_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_752_, uint8_t v_bi_753_, lean_object* v_type_754_, lean_object* v_k_755_, uint8_t v_kind_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___f_764_; lean_object* v___x_765_; 
lean_inc(v___y_757_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_764_, 0, v_k_755_);
lean_closure_set(v___f_764_, 1, v___y_757_);
lean_closure_set(v___f_764_, 2, v___y_758_);
v___x_765_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_752_, v_bi_753_, v_type_754_, v___f_764_, v_kind_756_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_a_774_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_765_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_765_);
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
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_782_, lean_object* v_bi_783_, lean_object* v_type_784_, lean_object* v_k_785_, lean_object* v_kind_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_bi_boxed_794_; uint8_t v_kind_boxed_795_; lean_object* v_res_796_; 
v_bi_boxed_794_ = lean_unbox(v_bi_783_);
v_kind_boxed_795_ = lean_unbox(v_kind_786_);
v_res_796_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_782_, v_bi_boxed_794_, v_type_784_, v_k_785_, v_kind_boxed_795_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_787_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_797_);
lean_ctor_set(v___x_804_, 1, v___y_798_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_814_, lean_object* v_type_815_, lean_object* v_val_816_, lean_object* v_k_817_, uint8_t v_nondep_818_, uint8_t v_kind_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; 
lean_inc(v___y_820_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_827_, 0, v_k_817_);
lean_closure_set(v___f_827_, 1, v___y_820_);
lean_closure_set(v___f_827_, 2, v___y_821_);
v___x_828_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_814_, v_type_815_, v_val_816_, v___f_827_, v_nondep_818_, v_kind_819_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
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
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_845_, lean_object* v_type_846_, lean_object* v_val_847_, lean_object* v_k_848_, lean_object* v_nondep_849_, lean_object* v_kind_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v_nondep_boxed_858_; uint8_t v_kind_boxed_859_; lean_object* v_res_860_; 
v_nondep_boxed_858_ = lean_unbox(v_nondep_849_);
v_kind_boxed_859_ = lean_unbox(v_kind_850_);
v_res_860_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_845_, v_type_846_, v_val_847_, v_k_848_, v_nondep_boxed_858_, v_kind_boxed_859_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_dec(v_b_862_);
lean_dec_ref(v_a_861_);
return v_x_863_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_878_; 
v_key_864_ = lean_ctor_get(v_x_863_, 0);
v_value_865_ = lean_ctor_get(v_x_863_, 1);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_868_ = v_x_863_;
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_tail_866_);
lean_inc(v_value_865_);
lean_inc(v_key_864_);
lean_dec(v_x_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_ExprStructEq_beq(v_key_864_, v_a_861_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_861_, v_b_862_, v_tail_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_key_864_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_value_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v_value_865_);
lean_dec(v_key_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_b_862_);
lean_ctor_set(v___x_868_, 0, v_a_861_);
v___x_876_ = v___x_868_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_b_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_tail_866_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
else
{
lean_object* v_key_882_; lean_object* v_tail_883_; uint8_t v___x_884_; 
v_key_882_ = lean_ctor_get(v_x_880_, 0);
v_tail_883_ = lean_ctor_get(v_x_880_, 2);
v___x_884_ = l_Lean_ExprStructEq_beq(v_key_882_, v_a_879_);
if (v___x_884_ == 0)
{
v_x_880_ = v_tail_883_;
goto _start;
}
else
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec_ref(v_a_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
return v_x_890_;
}
else
{
lean_object* v_key_892_; lean_object* v_value_893_; lean_object* v_tail_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_917_; 
v_key_892_ = lean_ctor_get(v_x_891_, 0);
v_value_893_ = lean_ctor_get(v_x_891_, 1);
v_tail_894_ = lean_ctor_get(v_x_891_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_917_ == 0)
{
v___x_896_ = v_x_891_;
v_isShared_897_ = v_isSharedCheck_917_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_tail_894_);
lean_inc(v_value_893_);
lean_inc(v_key_892_);
lean_dec(v_x_891_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_917_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v_fold_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_898_ = lean_array_get_size(v_x_890_);
v___x_899_ = l_Lean_ExprStructEq_hash(v_key_892_);
v___x_900_ = 32ULL;
v___x_901_ = lean_uint64_shift_right(v___x_899_, v___x_900_);
v_fold_902_ = lean_uint64_xor(v___x_899_, v___x_901_);
v___x_903_ = 16ULL;
v___x_904_ = lean_uint64_shift_right(v_fold_902_, v___x_903_);
v___x_905_ = lean_uint64_xor(v_fold_902_, v___x_904_);
v___x_906_ = lean_uint64_to_usize(v___x_905_);
v___x_907_ = lean_usize_of_nat(v___x_898_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_sub(v___x_907_, v___x_908_);
v___x_910_ = lean_usize_land(v___x_906_, v___x_909_);
v___x_911_ = lean_array_uget_borrowed(v_x_890_, v___x_910_);
lean_inc(v___x_911_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_911_);
v___x_913_ = v___x_896_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_key_892_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_value_893_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v___x_911_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_array_uset(v_x_890_, v___x_910_, v___x_913_);
v_x_890_ = v___x_914_;
v_x_891_ = v_tail_894_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_918_, lean_object* v_source_919_, lean_object* v_target_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_array_get_size(v_source_919_);
v___x_922_ = lean_nat_dec_lt(v_i_918_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_source_919_);
lean_dec(v_i_918_);
return v_target_920_;
}
else
{
lean_object* v_es_923_; lean_object* v___x_924_; lean_object* v_source_925_; lean_object* v_target_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_es_923_ = lean_array_fget(v_source_919_, v_i_918_);
v___x_924_ = lean_box(0);
v_source_925_ = lean_array_fset(v_source_919_, v_i_918_, v___x_924_);
v_target_926_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_920_, v_es_923_);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_i_918_, v___x_927_);
lean_dec(v_i_918_);
v_i_918_ = v___x_928_;
v_source_919_ = v_source_925_;
v_target_920_ = v_target_926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v_nbuckets_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_931_ = lean_array_get_size(v_data_930_);
v___x_932_ = lean_unsigned_to_nat(2u);
v_nbuckets_933_ = lean_nat_mul(v___x_931_, v___x_932_);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_box(0);
v___x_936_ = lean_mk_array(v_nbuckets_933_, v___x_935_);
v___x_937_ = lean_array_propagate_mark(v_data_930_, v___x_936_);
v___x_938_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_934_, v_data_930_, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
lean_object* v_size_942_; lean_object* v_buckets_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_986_; 
v_size_942_ = lean_ctor_get(v_m_939_, 0);
v_buckets_943_ = lean_ctor_get(v_m_939_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_m_939_);
if (v_isSharedCheck_986_ == 0)
{
v___x_945_ = v_m_939_;
v_isShared_946_ = v_isSharedCheck_986_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_buckets_943_);
lean_inc(v_size_942_);
lean_dec(v_m_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_986_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v_fold_951_; uint64_t v___x_952_; uint64_t v___x_953_; uint64_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; lean_object* v_bkt_960_; uint8_t v___x_961_; 
v___x_947_ = lean_array_get_size(v_buckets_943_);
v___x_948_ = l_Lean_ExprStructEq_hash(v_a_940_);
v___x_949_ = 32ULL;
v___x_950_ = lean_uint64_shift_right(v___x_948_, v___x_949_);
v_fold_951_ = lean_uint64_xor(v___x_948_, v___x_950_);
v___x_952_ = 16ULL;
v___x_953_ = lean_uint64_shift_right(v_fold_951_, v___x_952_);
v___x_954_ = lean_uint64_xor(v_fold_951_, v___x_953_);
v___x_955_ = lean_uint64_to_usize(v___x_954_);
v___x_956_ = lean_usize_of_nat(v___x_947_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_sub(v___x_956_, v___x_957_);
v___x_959_ = lean_usize_land(v___x_955_, v___x_958_);
v_bkt_960_ = lean_array_uget_borrowed(v_buckets_943_, v___x_959_);
v___x_961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_940_, v_bkt_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v_size_x27_963_; lean_object* v___x_964_; lean_object* v_buckets_x27_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v_size_x27_963_ = lean_nat_add(v_size_942_, v___x_962_);
lean_dec(v_size_942_);
lean_inc(v_bkt_960_);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v_a_940_);
lean_ctor_set(v___x_964_, 1, v_b_941_);
lean_ctor_set(v___x_964_, 2, v_bkt_960_);
v_buckets_x27_965_ = lean_array_uset(v_buckets_943_, v___x_959_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_nat_mul(v_size_x27_963_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(3u);
v___x_969_ = lean_nat_div(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_array_get_size(v_buckets_x27_965_);
v___x_971_ = lean_nat_dec_le(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
if (v___x_971_ == 0)
{
lean_object* v_val_972_; lean_object* v___x_974_; 
v_val_972_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_965_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_val_972_);
lean_ctor_set(v___x_945_, 0, v_size_x27_963_);
v___x_974_ = v___x_945_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_val_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_977_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_buckets_x27_965_);
lean_ctor_set(v___x_945_, 0, v_size_x27_963_);
v___x_977_ = v___x_945_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_buckets_x27_965_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
lean_inc(v_bkt_960_);
v___x_979_ = lean_box(0);
v_buckets_x27_980_ = lean_array_uset(v_buckets_943_, v___x_959_, v___x_979_);
v___x_981_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_940_, v_b_941_, v_bkt_960_);
v___x_982_ = lean_array_uset(v_buckets_x27_980_, v___x_959_, v___x_981_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_982_);
v___x_984_ = v___x_945_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_size_942_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_987_, lean_object* v_e_988_, lean_object* v_fst_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_st_ref_take(v_a_987_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_991_, v_e_988_, v_fst_989_);
v___x_994_ = lean_st_ref_put(v_a_987_, v___x_993_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_995_, lean_object* v_e_996_, lean_object* v_fst_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_995_, v_e_996_, v_fst_997_);
lean_dec(v_a_995_);
return v_res_999_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = l_Lean_maxRecDepthErrorMessage;
v___x_1006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1008_ = l_Lean_MessageData_ofFormat(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1010_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1011_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_ref_1012_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___y_1029_; lean_object* v_toCold_1046_; lean_object* v_currRecDepth_1047_; lean_object* v_ref_1048_; uint8_t v_diag_1049_; uint8_t v_suppressElabErrors_1050_; lean_object* v_maxRecDepth_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_toCold_1046_ = lean_ctor_get(v___y_1025_, 0);
v_currRecDepth_1047_ = lean_ctor_get(v___y_1025_, 1);
v_ref_1048_ = lean_ctor_get(v___y_1025_, 2);
v_diag_1049_ = lean_ctor_get_uint8(v___y_1025_, sizeof(void*)*3);
v_suppressElabErrors_1050_ = lean_ctor_get_uint8(v___y_1025_, sizeof(void*)*3 + 1);
v_maxRecDepth_1056_ = lean_ctor_get(v_toCold_1046_, 3);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_nat_dec_eq(v_maxRecDepth_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_eq(v_currRecDepth_1047_, v_maxRecDepth_1056_);
if (v___x_1059_ == 0)
{
goto v___jp_1051_;
}
else
{
lean_object* v___x_1060_; 
lean_dec(v___y_1022_);
lean_dec_ref(v_x_1020_);
lean_inc(v_ref_1048_);
v___x_1060_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1048_);
v___y_1029_ = v___x_1060_;
goto v___jp_1028_;
}
}
else
{
goto v___jp_1051_;
}
v___jp_1028_:
{
if (lean_obj_tag(v___y_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___y_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___y_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___y_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___y_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___y_1029_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1029_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___y_1029_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___y_1029_);
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
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_1051_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_currRecDepth_1047_, v___x_1052_);
lean_inc(v_ref_1048_);
lean_inc_ref(v_toCold_1046_);
v___x_1054_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1054_, 0, v_toCold_1046_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_ctor_set(v___x_1054_, 2, v_ref_1048_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*3, v_diag_1049_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*3 + 1, v_suppressElabErrors_1050_);
lean_inc(v___y_1026_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1021_);
v___x_1055_ = lean_apply_7(v_x_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___x_1054_, v___y_1026_, lean_box(0));
v___y_1029_ = v___x_1055_;
goto v___jp_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1062_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_box(0);
return v___x_1072_;
}
else
{
lean_object* v_key_1073_; lean_object* v_value_1074_; lean_object* v_tail_1075_; uint8_t v___x_1076_; 
v_key_1073_ = lean_ctor_get(v_x_1071_, 0);
v_value_1074_ = lean_ctor_get(v_x_1071_, 1);
v_tail_1075_ = lean_ctor_get(v_x_1071_, 2);
v___x_1076_ = l_Lean_ExprStructEq_beq(v_key_1073_, v_a_1070_);
if (v___x_1076_ == 0)
{
v_x_1071_ = v_tail_1075_;
goto _start;
}
else
{
lean_object* v___x_1078_; 
lean_inc(v_value_1074_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_value_1074_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1079_, v_x_1080_);
lean_dec(v_x_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_buckets_1084_; lean_object* v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v_fold_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_buckets_1084_ = lean_ctor_get(v_m_1082_, 1);
v___x_1085_ = lean_array_get_size(v_buckets_1084_);
v___x_1086_ = l_Lean_ExprStructEq_hash(v_a_1083_);
v___x_1087_ = 32ULL;
v___x_1088_ = lean_uint64_shift_right(v___x_1086_, v___x_1087_);
v_fold_1089_ = lean_uint64_xor(v___x_1086_, v___x_1088_);
v___x_1090_ = 16ULL;
v___x_1091_ = lean_uint64_shift_right(v_fold_1089_, v___x_1090_);
v___x_1092_ = lean_uint64_xor(v_fold_1089_, v___x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = lean_usize_of_nat(v___x_1085_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_sub(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_usize_land(v___x_1093_, v___x_1096_);
v___x_1098_ = lean_array_uget_borrowed(v_buckets_1084_, v___x_1097_);
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1083_, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1100_, v_a_1101_);
lean_dec_ref(v_a_1101_);
lean_dec_ref(v_m_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_apply_1(v_x_1104_, lean_box(0));
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___y_1105_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1114_, v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1123_, lean_object* v_pre_1124_, lean_object* v_post_1125_, lean_object* v_usedLetOnly_1126_, lean_object* v_skipConstInApp_1127_, lean_object* v_skipInstances_1128_, lean_object* v_body_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v_usedLetOnly_boxed_1138_; uint8_t v_skipConstInApp_boxed_1139_; uint8_t v_skipInstances_boxed_1140_; lean_object* v_res_1141_; 
v_usedLetOnly_boxed_1138_ = lean_unbox(v_usedLetOnly_1126_);
v_skipConstInApp_boxed_1139_ = lean_unbox(v_skipConstInApp_1127_);
v_skipInstances_boxed_1140_ = lean_unbox(v_skipInstances_1128_);
v_res_1141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1123_, v_pre_1124_, v_post_1125_, v_usedLetOnly_boxed_1138_, v_skipConstInApp_boxed_1139_, v_skipInstances_boxed_1140_, v_body_1129_, v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1145_, lean_object* v_pre_1146_, lean_object* v_post_1147_, uint8_t v_usedLetOnly_1148_, uint8_t v_skipConstInApp_1149_, uint8_t v_skipInstances_1150_, lean_object* v_body_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_array_push(v_fvars_1145_, v_x_1152_);
v___x_1161_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1146_, v_post_1147_, v_usedLetOnly_1148_, v_skipConstInApp_1149_, v_skipInstances_1150_, v___x_1160_, v_body_1151_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1162_, lean_object* v_pre_1163_, lean_object* v_post_1164_, lean_object* v_usedLetOnly_1165_, lean_object* v_skipConstInApp_1166_, lean_object* v_skipInstances_1167_, lean_object* v_body_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_usedLetOnly_boxed_1177_; uint8_t v_skipConstInApp_boxed_1178_; uint8_t v_skipInstances_boxed_1179_; lean_object* v_res_1180_; 
v_usedLetOnly_boxed_1177_ = lean_unbox(v_usedLetOnly_1165_);
v_skipConstInApp_boxed_1178_ = lean_unbox(v_skipConstInApp_1166_);
v_skipInstances_boxed_1179_ = lean_unbox(v_skipInstances_1167_);
v_res_1180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1162_, v_pre_1163_, v_post_1164_, v_usedLetOnly_boxed_1177_, v_skipConstInApp_boxed_1178_, v_skipInstances_boxed_1179_, v_body_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1170_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1181_, lean_object* v_post_1182_, uint8_t v_usedLetOnly_1183_, uint8_t v_skipConstInApp_1184_, uint8_t v_skipInstances_1185_, lean_object* v_e_1186_, lean_object* v_a_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
lean_inc_ref(v_post_1182_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc_ref(v_e_1186_);
v___x_1194_ = lean_apply_7(v_post_1182_, v_e_1186_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, lean_box(0));
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1226_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1226_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1226_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1225_; 
v_fst_1199_ = lean_ctor_get(v_a_1195_, 0);
v_snd_1200_ = lean_ctor_get(v_a_1195_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1202_ = v_a_1195_;
v_isShared_1203_ = v_isSharedCheck_1225_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snd_1200_);
lean_inc(v_fst_1199_);
lean_dec(v_a_1195_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1225_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___y_1205_; 
switch(lean_obj_tag(v_fst_1199_))
{
case 0:
{
lean_object* v_e_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1202_);
lean_del_object(v___x_1197_);
lean_dec_ref(v_e_1186_);
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v_e_1212_ = lean_ctor_get(v_fst_1199_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_fst_1199_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v_fst_1199_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_e_1212_);
lean_dec(v_fst_1199_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_e_1212_);
lean_ctor_set(v___x_1216_, 1, v_snd_1200_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
case 1:
{
lean_object* v_e_1221_; lean_object* v___x_1222_; 
lean_del_object(v___x_1202_);
lean_del_object(v___x_1197_);
lean_dec_ref(v_e_1186_);
v_e_1221_ = lean_ctor_get(v_fst_1199_, 0);
lean_inc_ref(v_e_1221_);
lean_dec_ref_known(v_fst_1199_, 1);
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1181_, v_post_1182_, v_usedLetOnly_1183_, v_skipConstInApp_1184_, v_skipInstances_1185_, v_e_1221_, v_a_1187_, v_snd_1200_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1222_;
}
default: 
{
lean_object* v_e_x3f_1223_; 
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v_e_x3f_1223_ = lean_ctor_get(v_fst_1199_, 0);
lean_inc(v_e_x3f_1223_);
lean_dec_ref_known(v_fst_1199_, 1);
if (lean_obj_tag(v_e_x3f_1223_) == 0)
{
v___y_1205_ = v_e_1186_;
goto v___jp_1204_;
}
else
{
lean_object* v_val_1224_; 
lean_dec_ref(v_e_1186_);
v_val_1224_ = lean_ctor_get(v_e_x3f_1223_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_e_x3f_1223_, 1);
v___y_1205_ = v_val_1224_;
goto v___jp_1204_;
}
}
}
v___jp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___y_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___y_1205_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_snd_1200_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1207_);
v___x_1209_ = v___x_1197_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v_e_1186_);
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v_a_1227_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1194_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1194_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1235_, lean_object* v_post_1236_, uint8_t v_usedLetOnly_1237_, uint8_t v_skipConstInApp_1238_, uint8_t v_skipInstances_1239_, lean_object* v_fvars_1240_, lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
if (lean_obj_tag(v_e_1241_) == 6)
{
lean_object* v_binderName_1249_; lean_object* v_binderType_1250_; lean_object* v_body_1251_; uint8_t v_binderInfo_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_binderName_1249_ = lean_ctor_get(v_e_1241_, 0);
lean_inc(v_binderName_1249_);
v_binderType_1250_ = lean_ctor_get(v_e_1241_, 1);
lean_inc_ref(v_binderType_1250_);
v_body_1251_ = lean_ctor_get(v_e_1241_, 2);
lean_inc_ref(v_body_1251_);
v_binderInfo_1252_ = lean_ctor_get_uint8(v_e_1241_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1253_ = lean_box(v_usedLetOnly_1237_);
v___x_1254_ = lean_box(v_skipConstInApp_1238_);
v___x_1255_ = lean_box(v_skipInstances_1239_);
lean_inc_ref(v_post_1236_);
lean_inc_ref(v_pre_1235_);
lean_inc_ref(v_fvars_1240_);
v___f_1256_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1256_, 0, v_fvars_1240_);
lean_closure_set(v___f_1256_, 1, v_pre_1235_);
lean_closure_set(v___f_1256_, 2, v_post_1236_);
lean_closure_set(v___f_1256_, 3, v___x_1253_);
lean_closure_set(v___f_1256_, 4, v___x_1254_);
lean_closure_set(v___f_1256_, 5, v___x_1255_);
lean_closure_set(v___f_1256_, 6, v_body_1251_);
v___x_1257_ = lean_expr_instantiate_rev(v_binderType_1250_, v_fvars_1240_);
lean_dec_ref(v_fvars_1240_);
lean_dec_ref(v_binderType_1250_);
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1235_, v_post_1236_, v_usedLetOnly_1237_, v_skipConstInApp_1238_, v_skipInstances_1239_, v___x_1257_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_fst_1260_ = lean_ctor_get(v_a_1259_, 0);
lean_inc(v_fst_1260_);
v_snd_1261_ = lean_ctor_get(v_a_1259_, 1);
lean_inc(v_snd_1261_);
lean_dec(v_a_1259_);
v___x_1262_ = 0;
v___x_1263_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1249_, v_binderInfo_1252_, v_fst_1260_, v___f_1256_, v___x_1262_, v_a_1242_, v_snd_1261_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1263_;
}
else
{
lean_dec_ref(v___f_1256_);
lean_dec(v_binderName_1249_);
return v___x_1258_;
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_expr_instantiate_rev(v_e_1241_, v_fvars_1240_);
lean_dec_ref(v_e_1241_);
lean_inc_ref(v_post_1236_);
lean_inc_ref(v_pre_1235_);
v___x_1265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1235_, v_post_1236_, v_usedLetOnly_1237_, v_skipConstInApp_1238_, v_skipInstances_1239_, v___x_1264_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_fst_1267_; lean_object* v_snd_1268_; uint8_t v___x_1269_; uint8_t v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v_fst_1267_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_fst_1267_);
v_snd_1268_ = lean_ctor_get(v_a_1266_, 1);
lean_inc(v_snd_1268_);
lean_dec(v_a_1266_);
v___x_1269_ = 0;
v___x_1270_ = 1;
v___x_1271_ = 1;
v___x_1272_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1240_, v_fst_1267_, v___x_1269_, v_usedLetOnly_1237_, v___x_1269_, v___x_1270_, v___x_1271_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec_ref(v_fvars_1240_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1235_, v_post_1236_, v_usedLetOnly_1237_, v_skipConstInApp_1238_, v_skipInstances_1239_, v_a_1273_, v_a_1242_, v_snd_1268_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1274_;
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_snd_1268_);
lean_dec_ref(v_post_1236_);
lean_dec_ref(v_pre_1235_);
v_a_1275_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1272_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1240_);
lean_dec_ref(v_post_1236_);
lean_dec_ref(v_pre_1235_);
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1283_, lean_object* v_pre_1284_, lean_object* v_post_1285_, uint8_t v_usedLetOnly_1286_, uint8_t v_skipConstInApp_1287_, uint8_t v_skipInstances_1288_, lean_object* v_body_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_array_push(v_fvars_1283_, v_x_1290_);
v___x_1299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1284_, v_post_1285_, v_usedLetOnly_1286_, v_skipConstInApp_1287_, v_skipInstances_1288_, v___x_1298_, v_body_1289_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1300_, lean_object* v_pre_1301_, lean_object* v_post_1302_, lean_object* v_usedLetOnly_1303_, lean_object* v_skipConstInApp_1304_, lean_object* v_skipInstances_1305_, lean_object* v_body_1306_, lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_usedLetOnly_boxed_1315_; uint8_t v_skipConstInApp_boxed_1316_; uint8_t v_skipInstances_boxed_1317_; lean_object* v_res_1318_; 
v_usedLetOnly_boxed_1315_ = lean_unbox(v_usedLetOnly_1303_);
v_skipConstInApp_boxed_1316_ = lean_unbox(v_skipConstInApp_1304_);
v_skipInstances_boxed_1317_ = lean_unbox(v_skipInstances_1305_);
v_res_1318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1300_, v_pre_1301_, v_post_1302_, v_usedLetOnly_boxed_1315_, v_skipConstInApp_boxed_1316_, v_skipInstances_boxed_1317_, v_body_1306_, v_x_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1308_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1319_, lean_object* v_post_1320_, uint8_t v_usedLetOnly_1321_, uint8_t v_skipConstInApp_1322_, uint8_t v_skipInstances_1323_, lean_object* v_fvars_1324_, lean_object* v_e_1325_, lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
if (lean_obj_tag(v_e_1325_) == 8)
{
lean_object* v_declName_1333_; lean_object* v_type_1334_; lean_object* v_value_1335_; lean_object* v_body_1336_; uint8_t v_nondep_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_declName_1333_ = lean_ctor_get(v_e_1325_, 0);
lean_inc(v_declName_1333_);
v_type_1334_ = lean_ctor_get(v_e_1325_, 1);
lean_inc_ref(v_type_1334_);
v_value_1335_ = lean_ctor_get(v_e_1325_, 2);
lean_inc_ref(v_value_1335_);
v_body_1336_ = lean_ctor_get(v_e_1325_, 3);
lean_inc_ref(v_body_1336_);
v_nondep_1337_ = lean_ctor_get_uint8(v_e_1325_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1325_, 4);
v___x_1338_ = lean_box(v_usedLetOnly_1321_);
v___x_1339_ = lean_box(v_skipConstInApp_1322_);
v___x_1340_ = lean_box(v_skipInstances_1323_);
lean_inc_ref_n(v_post_1320_, 2);
lean_inc_ref_n(v_pre_1319_, 2);
lean_inc_ref(v_fvars_1324_);
v___f_1341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1341_, 0, v_fvars_1324_);
lean_closure_set(v___f_1341_, 1, v_pre_1319_);
lean_closure_set(v___f_1341_, 2, v_post_1320_);
lean_closure_set(v___f_1341_, 3, v___x_1338_);
lean_closure_set(v___f_1341_, 4, v___x_1339_);
lean_closure_set(v___f_1341_, 5, v___x_1340_);
lean_closure_set(v___f_1341_, 6, v_body_1336_);
v___x_1342_ = lean_expr_instantiate_rev(v_type_1334_, v_fvars_1324_);
lean_dec_ref(v_type_1334_);
v___x_1343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v___x_1342_, v_a_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v_fst_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec(v_a_1344_);
v___x_1347_ = lean_expr_instantiate_rev(v_value_1335_, v_fvars_1324_);
lean_dec_ref(v_fvars_1324_);
lean_dec_ref(v_value_1335_);
v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v___x_1347_, v_a_1326_, v_snd_1346_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v_fst_1350_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_fst_1350_);
v_snd_1351_ = lean_ctor_get(v_a_1349_, 1);
lean_inc(v_snd_1351_);
lean_dec(v_a_1349_);
v___x_1352_ = 0;
v___x_1353_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1333_, v_fst_1345_, v_fst_1350_, v___f_1341_, v_nondep_1337_, v___x_1352_, v_a_1326_, v_snd_1351_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1353_;
}
else
{
lean_dec(v_fst_1345_);
lean_dec_ref(v___f_1341_);
lean_dec(v_declName_1333_);
return v___x_1348_;
}
}
else
{
lean_dec_ref(v___f_1341_);
lean_dec_ref(v_value_1335_);
lean_dec(v_declName_1333_);
lean_dec_ref(v_fvars_1324_);
lean_dec_ref(v_post_1320_);
lean_dec_ref(v_pre_1319_);
return v___x_1343_;
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_expr_instantiate_rev(v_e_1325_, v_fvars_1324_);
lean_dec_ref(v_e_1325_);
lean_inc_ref(v_post_1320_);
lean_inc_ref(v_pre_1319_);
v___x_1355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v___x_1354_, v_a_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v_fst_1357_; lean_object* v_snd_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v_fst_1357_ = lean_ctor_get(v_a_1356_, 0);
lean_inc(v_fst_1357_);
v_snd_1358_ = lean_ctor_get(v_a_1356_, 1);
lean_inc(v_snd_1358_);
lean_dec(v_a_1356_);
v___x_1359_ = 0;
v___x_1360_ = 1;
v___x_1361_ = l_Lean_Meta_mkLetFVars(v_fvars_1324_, v_fst_1357_, v_usedLetOnly_1321_, v___x_1359_, v___x_1360_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v_fvars_1324_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v_a_1362_, v_a_1326_, v_snd_1358_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1363_;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_snd_1358_);
lean_dec_ref(v_post_1320_);
lean_dec_ref(v_pre_1319_);
v_a_1364_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1361_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1361_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1324_);
lean_dec_ref(v_post_1320_);
lean_dec_ref(v_pre_1319_);
return v___x_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1372_, lean_object* v_post_1373_, uint8_t v_usedLetOnly_1374_, uint8_t v_skipConstInApp_1375_, uint8_t v_skipInstances_1376_, size_t v_sz_1377_, size_t v_i_1378_, lean_object* v_bs_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v___x_1387_; 
v___x_1387_ = lean_usize_dec_lt(v_i_1378_, v_sz_1377_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_post_1373_);
lean_dec_ref(v_pre_1372_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_bs_1379_);
lean_ctor_set(v___x_1388_, 1, v___y_1381_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; lean_object* v___x_1393_; 
v_v_1390_ = lean_array_uget(v_bs_1379_, v_i_1378_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1379_, v_i_1378_, v___x_1391_);
lean_inc_ref(v_post_1373_);
lean_inc_ref(v_pre_1372_);
v___x_1393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1372_, v_post_1373_, v_usedLetOnly_1374_, v_skipConstInApp_1375_, v_skipInstances_1376_, v_v_1390_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_fst_1395_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_fst_1395_);
v_snd_1396_ = lean_ctor_get(v_a_1394_, 1);
lean_inc(v_snd_1396_);
lean_dec(v_a_1394_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1378_, v___x_1397_);
v___x_1399_ = lean_array_uset(v_bs_x27_1392_, v_i_1378_, v_fst_1395_);
v_i_1378_ = v___x_1398_;
v_bs_1379_ = v___x_1399_;
v___y_1381_ = v_snd_1396_;
goto _start;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_bs_x27_1392_);
lean_dec_ref(v_post_1373_);
lean_dec_ref(v_pre_1372_);
v_a_1401_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1393_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1393_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1409_, lean_object* v_post_1410_, uint8_t v_usedLetOnly_1411_, uint8_t v_skipConstInApp_1412_, uint8_t v_skipInstances_1413_, lean_object* v___x_1414_, lean_object* v___y_1415_, lean_object* v_b_1416_, lean_object* v_a_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1409_, v_post_1410_, v_usedLetOnly_1411_, v_skipConstInApp_1412_, v_skipInstances_1413_, v___x_1414_, v___y_1415_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1443_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1443_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1443_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1442_; 
v_fst_1429_ = lean_ctor_get(v_a_1425_, 0);
v_snd_1430_ = lean_ctor_get(v_a_1425_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1425_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1432_ = v_a_1425_;
v_isShared_1433_ = v_isSharedCheck_1442_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_inc(v_fst_1429_);
lean_dec(v_a_1425_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1442_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_array_fset(v_b_1416_, v_a_1417_, v_fst_1429_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_snd_1430_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1437_);
v___x_1439_ = v___x_1427_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_b_1416_);
v_a_1444_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1424_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1424_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1452_, lean_object* v_post_1453_, lean_object* v_usedLetOnly_1454_, lean_object* v_skipConstInApp_1455_, lean_object* v_skipInstances_1456_, lean_object* v___x_1457_, lean_object* v___y_1458_, lean_object* v_b_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_usedLetOnly_boxed_1467_; uint8_t v_skipConstInApp_boxed_1468_; uint8_t v_skipInstances_boxed_1469_; lean_object* v_res_1470_; 
v_usedLetOnly_boxed_1467_ = lean_unbox(v_usedLetOnly_1454_);
v_skipConstInApp_boxed_1468_ = lean_unbox(v_skipConstInApp_1455_);
v_skipInstances_boxed_1469_ = lean_unbox(v_skipInstances_1456_);
v_res_1470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1452_, v_post_1453_, v_usedLetOnly_boxed_1467_, v_skipConstInApp_boxed_1468_, v_skipInstances_boxed_1469_, v___x_1457_, v___y_1458_, v_b_1459_, v_a_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_a_1460_);
lean_dec(v___y_1458_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1471_, lean_object* v___x_1472_, lean_object* v_pre_1473_, lean_object* v_post_1474_, uint8_t v_usedLetOnly_1475_, uint8_t v_skipConstInApp_1476_, uint8_t v_skipInstances_1477_, lean_object* v_a_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___y_1488_; uint8_t v___x_1522_; 
v___x_1522_ = lean_nat_dec_lt(v_a_1478_, v_upperBound_1471_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_a_1478_);
lean_dec_ref(v_post_1474_);
lean_dec_ref(v_pre_1473_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1479_);
lean_ctor_set(v___x_1523_, 1, v___y_1481_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_array_fget_borrowed(v_b_1479_, v_a_1478_);
v___x_1526_ = lean_array_get_size(v___x_1472_);
v___x_1527_ = lean_nat_dec_lt(v_a_1478_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; 
lean_inc(v___x_1525_);
v___x_1528_ = lean_box(v_usedLetOnly_1475_);
v___x_1529_ = lean_box(v_skipConstInApp_1476_);
v___x_1530_ = lean_box(v_skipInstances_1477_);
lean_inc(v_a_1478_);
lean_inc(v___y_1480_);
lean_inc_ref(v_post_1474_);
lean_inc_ref(v_pre_1473_);
v___f_1531_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1531_, 0, v_pre_1473_);
lean_closure_set(v___f_1531_, 1, v_post_1474_);
lean_closure_set(v___f_1531_, 2, v___x_1528_);
lean_closure_set(v___f_1531_, 3, v___x_1529_);
lean_closure_set(v___f_1531_, 4, v___x_1530_);
lean_closure_set(v___f_1531_, 5, v___x_1525_);
lean_closure_set(v___f_1531_, 6, v___y_1480_);
lean_closure_set(v___f_1531_, 7, v_b_1479_);
lean_closure_set(v___f_1531_, 8, v_a_1478_);
v___y_1488_ = v___f_1531_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1532_; uint8_t v_isInstance_1533_; 
v___x_1532_ = lean_array_fget_borrowed(v___x_1472_, v_a_1478_);
v_isInstance_1533_ = lean_ctor_get_uint8(v___x_1532_, sizeof(void*)*1 + 4);
if (v_isInstance_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; 
lean_inc(v___x_1525_);
v___x_1534_ = lean_box(v_usedLetOnly_1475_);
v___x_1535_ = lean_box(v_skipConstInApp_1476_);
v___x_1536_ = lean_box(v_skipInstances_1477_);
lean_inc(v_a_1478_);
lean_inc(v___y_1480_);
lean_inc_ref(v_post_1474_);
lean_inc_ref(v_pre_1473_);
v___f_1537_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1537_, 0, v_pre_1473_);
lean_closure_set(v___f_1537_, 1, v_post_1474_);
lean_closure_set(v___f_1537_, 2, v___x_1534_);
lean_closure_set(v___f_1537_, 3, v___x_1535_);
lean_closure_set(v___f_1537_, 4, v___x_1536_);
lean_closure_set(v___f_1537_, 5, v___x_1525_);
lean_closure_set(v___f_1537_, 6, v___y_1480_);
lean_closure_set(v___f_1537_, 7, v_b_1479_);
lean_closure_set(v___f_1537_, 8, v_a_1478_);
v___y_1488_ = v___f_1537_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1538_; lean_object* v___f_1539_; 
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_b_1479_);
v___f_1539_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1539_, 0, v___x_1538_);
v___y_1488_ = v___f_1539_;
goto v___jp_1487_;
}
}
}
v___jp_1487_:
{
lean_object* v___x_1489_; 
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
v___x_1489_ = lean_apply_6(v___y_1488_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1513_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_fst_1494_; 
v_fst_1494_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_fst_1494_);
if (lean_obj_tag(v_fst_1494_) == 0)
{
lean_object* v_snd_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1478_);
lean_dec_ref(v_post_1474_);
lean_dec_ref(v_pre_1473_);
v_snd_1495_ = lean_ctor_get(v_a_1490_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_a_1490_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_a_1490_, 0);
lean_dec(v_unused_1507_);
v___x_1497_ = v_a_1490_;
v_isShared_1498_ = v_isSharedCheck_1506_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1495_);
lean_dec(v_a_1490_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1506_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_a_1499_; lean_object* v___x_1501_; 
v_a_1499_ = lean_ctor_get(v_fst_1494_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_fst_1494_, 1);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_a_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_snd_1495_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1501_);
v___x_1503_ = v___x_1492_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_snd_1508_; lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_del_object(v___x_1492_);
v_snd_1508_ = lean_ctor_get(v_a_1490_, 1);
lean_inc(v_snd_1508_);
lean_dec(v_a_1490_);
v_a_1509_ = lean_ctor_get(v_fst_1494_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_fst_1494_, 1);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_add(v_a_1478_, v___x_1510_);
lean_dec(v_a_1478_);
v_a_1478_ = v___x_1511_;
v_b_1479_ = v_a_1509_;
v___y_1481_ = v_snd_1508_;
goto _start;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1478_);
lean_dec_ref(v_post_1474_);
lean_dec_ref(v_pre_1473_);
v_a_1514_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1489_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1489_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1540_, lean_object* v_pre_1541_, lean_object* v_post_1542_, uint8_t v_usedLetOnly_1543_, uint8_t v_skipConstInApp_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_f_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; 
if (lean_obj_tag(v_x_1545_) == 5)
{
lean_object* v_fn_1611_; lean_object* v_arg_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_fn_1611_ = lean_ctor_get(v_x_1545_, 0);
lean_inc_ref(v_fn_1611_);
v_arg_1612_ = lean_ctor_get(v_x_1545_, 1);
lean_inc_ref(v_arg_1612_);
lean_dec_ref_known(v_x_1545_, 2);
v___x_1613_ = lean_array_set(v_x_1546_, v_x_1547_, v_arg_1612_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_sub(v_x_1547_, v___x_1614_);
lean_dec(v_x_1547_);
v_x_1545_ = v_fn_1611_;
v_x_1546_ = v___x_1613_;
v_x_1547_ = v___x_1615_;
goto _start;
}
else
{
lean_dec(v_x_1547_);
if (v_skipConstInApp_1544_ == 0)
{
goto v___jp_1606_;
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_Expr_isConst(v_x_1545_);
if (v___x_1617_ == 0)
{
goto v___jp_1606_;
}
else
{
v_f_1556_ = v_x_1545_;
v___y_1557_ = v___y_1548_;
v___y_1558_ = v___y_1549_;
v___y_1559_ = v___y_1550_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
goto v___jp_1555_;
}
}
}
v___jp_1555_:
{
if (v_skipInstances_1540_ == 0)
{
size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v_sz_1563_ = lean_array_size(v_x_1546_);
v___x_1564_ = ((size_t)0ULL);
lean_inc_ref(v_post_1542_);
lean_inc_ref(v_pre_1541_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1541_, v_post_1542_, v_usedLetOnly_1543_, v_skipConstInApp_1544_, v_skipInstances_1540_, v_sz_1563_, v___x_1564_, v_x_1546_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_fst_1567_; lean_object* v_snd_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_fst_1567_ = lean_ctor_get(v_a_1566_, 0);
lean_inc(v_fst_1567_);
v_snd_1568_ = lean_ctor_get(v_a_1566_, 1);
lean_inc(v_snd_1568_);
lean_dec(v_a_1566_);
v___x_1569_ = l_Lean_mkAppN(v_f_1556_, v_fst_1567_);
lean_dec(v_fst_1567_);
v___x_1570_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1541_, v_post_1542_, v_usedLetOnly_1543_, v_skipConstInApp_1544_, v_skipInstances_1540_, v___x_1569_, v___y_1557_, v_snd_1568_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1570_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_f_1556_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_a_1571_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1565_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1565_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_array_get_size(v_x_1546_);
lean_inc_ref(v_f_1556_);
v___x_1580_ = l_Lean_Meta_getFunInfoNArgs(v_f_1556_, v___x_1579_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v_paramInfo_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v_paramInfo_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc_ref(v_paramInfo_1582_);
lean_dec(v_a_1581_);
v___x_1583_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1542_);
lean_inc_ref(v_pre_1541_);
v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1579_, v_paramInfo_1582_, v_pre_1541_, v_post_1542_, v_usedLetOnly_1543_, v_skipConstInApp_1544_, v_skipInstances_1540_, v___x_1583_, v_x_1546_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec_ref(v_paramInfo_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_fst_1586_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v_a_1585_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_a_1585_);
v___x_1588_ = l_Lean_mkAppN(v_f_1556_, v_fst_1586_);
lean_dec(v_fst_1586_);
v___x_1589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1541_, v_post_1542_, v_usedLetOnly_1543_, v_skipConstInApp_1544_, v_skipInstances_1540_, v___x_1588_, v___y_1557_, v_snd_1587_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1589_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_f_1556_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_a_1590_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1584_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1584_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v___y_1558_);
lean_dec_ref(v_f_1556_);
lean_dec_ref(v_x_1546_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_a_1598_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1580_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1580_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1607_; 
lean_inc_ref(v_post_1542_);
lean_inc_ref(v_pre_1541_);
v___x_1607_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1541_, v_post_1542_, v_usedLetOnly_1543_, v_skipConstInApp_1544_, v_skipInstances_1540_, v_x_1545_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_fst_1609_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v_a_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec(v_a_1608_);
v_f_1556_ = v_fst_1609_;
v___y_1557_ = v___y_1548_;
v___y_1558_ = v_snd_1610_;
v___y_1559_ = v___y_1550_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
goto v___jp_1555_;
}
else
{
lean_dec_ref(v_x_1546_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1618_, lean_object* v_pre_1619_, lean_object* v_e_1620_, lean_object* v_post_1621_, uint8_t v_usedLetOnly_1622_, uint8_t v_skipConstInApp_1623_, uint8_t v_skipInstances_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Core_checkSystem(v___x_1618_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref_known(v___x_1632_, 1);
lean_inc_ref(v_pre_1619_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc_ref(v_e_1620_);
v___x_1633_ = lean_apply_7(v_pre_1619_, v_e_1620_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1695_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1695_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1695_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_fst_1638_; lean_object* v_snd_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1694_; 
v_fst_1638_ = lean_ctor_get(v_a_1634_, 0);
v_snd_1639_ = lean_ctor_get(v_a_1634_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1641_ = v_a_1634_;
v_isShared_1642_ = v_isSharedCheck_1694_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_snd_1639_);
lean_inc(v_fst_1638_);
lean_dec(v_a_1634_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1694_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___y_1644_; 
switch(lean_obj_tag(v_fst_1638_))
{
case 0:
{
lean_object* v_e_1683_; lean_object* v___x_1685_; 
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_e_1620_);
lean_dec_ref(v_pre_1619_);
v_e_1683_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc_ref(v_e_1683_);
lean_dec_ref_known(v_fst_1638_, 1);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v_e_1683_);
v___x_1685_ = v___x_1641_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_e_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_snd_1639_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1685_);
v___x_1687_ = v___x_1636_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
case 1:
{
lean_object* v_e_1690_; lean_object* v___x_1691_; 
lean_del_object(v___x_1641_);
lean_del_object(v___x_1636_);
lean_dec_ref(v_e_1620_);
v_e_1690_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc_ref(v_e_1690_);
lean_dec_ref_known(v_fst_1638_, 1);
v___x_1691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v_e_1690_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1691_;
}
default: 
{
lean_object* v_e_x3f_1692_; 
lean_del_object(v___x_1641_);
lean_del_object(v___x_1636_);
v_e_x3f_1692_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc(v_e_x3f_1692_);
lean_dec_ref_known(v_fst_1638_, 1);
if (lean_obj_tag(v_e_x3f_1692_) == 0)
{
v___y_1644_ = v_e_1620_;
goto v___jp_1643_;
}
else
{
lean_object* v_val_1693_; 
lean_dec_ref(v_e_1620_);
v_val_1693_ = lean_ctor_get(v_e_x3f_1692_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v_e_x3f_1692_, 1);
v___y_1644_ = v_val_1693_;
goto v___jp_1643_;
}
}
}
v___jp_1643_:
{
switch(lean_obj_tag(v___y_1644_))
{
case 7:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1645_, v___y_1644_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1646_;
}
case 6:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1647_, v___y_1644_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1648_;
}
case 8:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1649_, v___y_1644_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1650_;
}
case 5:
{
lean_object* v_dummy_1651_; lean_object* v_nargs_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_dummy_1651_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1652_ = l_Lean_Expr_getAppNumArgs(v___y_1644_);
lean_inc(v_nargs_1652_);
v___x_1653_ = lean_mk_array(v_nargs_1652_, v_dummy_1651_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_sub(v_nargs_1652_, v___x_1654_);
lean_dec(v_nargs_1652_);
v___x_1656_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1624_, v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v___y_1644_, v___x_1653_, v___x_1655_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1656_;
}
case 10:
{
lean_object* v_data_1657_; lean_object* v_expr_1658_; lean_object* v___x_1659_; 
v_data_1657_ = lean_ctor_get(v___y_1644_, 0);
v_expr_1658_ = lean_ctor_get(v___y_1644_, 1);
lean_inc_ref(v_expr_1658_);
lean_inc_ref(v_post_1621_);
lean_inc_ref(v_pre_1619_);
v___x_1659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v_expr_1658_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; size_t v___x_1663_; size_t v___x_1664_; uint8_t v___x_1665_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_fst_1661_ = lean_ctor_get(v_a_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec(v_a_1660_);
v___x_1663_ = lean_ptr_addr(v_expr_1658_);
v___x_1664_ = lean_ptr_addr(v_fst_1661_);
v___x_1665_ = lean_usize_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_inc(v_data_1657_);
lean_dec_ref_known(v___y_1644_, 2);
v___x_1666_ = l_Lean_Expr_mdata___override(v_data_1657_, v_fst_1661_);
v___x_1667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1666_, v___y_1625_, v_snd_1662_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_fst_1661_);
v___x_1668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___y_1644_, v___y_1625_, v_snd_1662_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1668_;
}
}
else
{
lean_dec_ref_known(v___y_1644_, 2);
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_pre_1619_);
return v___x_1659_;
}
}
case 11:
{
lean_object* v_typeName_1669_; lean_object* v_idx_1670_; lean_object* v_struct_1671_; lean_object* v___x_1672_; 
v_typeName_1669_ = lean_ctor_get(v___y_1644_, 0);
v_idx_1670_ = lean_ctor_get(v___y_1644_, 1);
v_struct_1671_ = lean_ctor_get(v___y_1644_, 2);
lean_inc_ref(v_struct_1671_);
lean_inc_ref(v_post_1621_);
lean_inc_ref(v_pre_1619_);
v___x_1672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v_struct_1671_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v_fst_1674_; lean_object* v_snd_1675_; size_t v___x_1676_; size_t v___x_1677_; uint8_t v___x_1678_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v_fst_1674_ = lean_ctor_get(v_a_1673_, 0);
lean_inc(v_fst_1674_);
v_snd_1675_ = lean_ctor_get(v_a_1673_, 1);
lean_inc(v_snd_1675_);
lean_dec(v_a_1673_);
v___x_1676_ = lean_ptr_addr(v_struct_1671_);
v___x_1677_ = lean_ptr_addr(v_fst_1674_);
v___x_1678_ = lean_usize_dec_eq(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_inc(v_idx_1670_);
lean_inc(v_typeName_1669_);
lean_dec_ref_known(v___y_1644_, 3);
v___x_1679_ = l_Lean_Expr_proj___override(v_typeName_1669_, v_idx_1670_, v_fst_1674_);
v___x_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1679_, v___y_1625_, v_snd_1675_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; 
lean_dec(v_fst_1674_);
v___x_1681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___y_1644_, v___y_1625_, v_snd_1675_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1681_;
}
}
else
{
lean_dec_ref_known(v___y_1644_, 3);
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_pre_1619_);
return v___x_1672_;
}
}
default: 
{
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1619_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___y_1644_, v___y_1625_, v_snd_1639_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1682_;
}
}
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_e_1620_);
lean_dec_ref(v_pre_1619_);
v_a_1696_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1633_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1633_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v___y_1626_);
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_e_1620_);
lean_dec_ref(v_pre_1619_);
v_a_1704_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1632_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1632_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1712_, lean_object* v_pre_1713_, lean_object* v_e_1714_, lean_object* v_post_1715_, lean_object* v_usedLetOnly_1716_, lean_object* v_skipConstInApp_1717_, lean_object* v_skipInstances_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v_usedLetOnly_boxed_1726_; uint8_t v_skipConstInApp_boxed_1727_; uint8_t v_skipInstances_boxed_1728_; lean_object* v_res_1729_; 
v_usedLetOnly_boxed_1726_ = lean_unbox(v_usedLetOnly_1716_);
v_skipConstInApp_boxed_1727_ = lean_unbox(v_skipConstInApp_1717_);
v_skipInstances_boxed_1728_ = lean_unbox(v_skipInstances_1718_);
v_res_1729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1712_, v_pre_1713_, v_e_1714_, v_post_1715_, v_usedLetOnly_boxed_1726_, v_skipConstInApp_boxed_1727_, v_skipInstances_boxed_1728_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1719_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1730_, lean_object* v_post_1731_, uint8_t v_usedLetOnly_1732_, uint8_t v_skipConstInApp_1733_, uint8_t v_skipInstances_1734_, lean_object* v_e_1735_, lean_object* v_a_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_inc(v_a_1736_);
v___x_1743_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1743_, 0, lean_box(0));
lean_closure_set(v___x_1743_, 1, lean_box(0));
lean_closure_set(v___x_1743_, 2, v_a_1736_);
v___x_1744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1743_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1799_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1799_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1799_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1798_; 
v_fst_1749_ = lean_ctor_get(v_a_1745_, 0);
v_snd_1750_ = lean_ctor_get(v_a_1745_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_a_1745_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1752_ = v_a_1745_;
v_isShared_1753_ = v_isSharedCheck_1798_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snd_1750_);
lean_inc(v_fst_1749_);
lean_dec(v_a_1745_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1798_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1749_, v_e_1735_);
lean_dec(v_fst_1749_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; 
lean_del_object(v___x_1752_);
lean_del_object(v___x_1747_);
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1756_ = lean_box(v_usedLetOnly_1732_);
v___x_1757_ = lean_box(v_skipConstInApp_1733_);
v___x_1758_ = lean_box(v_skipInstances_1734_);
lean_inc_ref(v_e_1735_);
v___f_1759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1759_, 0, v___x_1755_);
lean_closure_set(v___f_1759_, 1, v_pre_1730_);
lean_closure_set(v___f_1759_, 2, v_e_1735_);
lean_closure_set(v___f_1759_, 3, v_post_1731_);
lean_closure_set(v___f_1759_, 4, v___x_1756_);
lean_closure_set(v___f_1759_, 5, v___x_1757_);
lean_closure_set(v___f_1759_, 6, v___x_1758_);
v___x_1760_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1759_, v_a_1736_, v_snd_1750_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v_fst_1762_ = lean_ctor_get(v_a_1761_, 0);
lean_inc_n(v_fst_1762_, 2);
v_snd_1763_ = lean_ctor_get(v_a_1761_, 1);
lean_inc(v_snd_1763_);
lean_dec(v_a_1761_);
lean_inc(v_a_1736_);
v___f_1764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1764_, 0, v_a_1736_);
lean_closure_set(v___f_1764_, 1, v_e_1735_);
lean_closure_set(v___f_1764_, 2, v_fst_1762_);
v___x_1765_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1764_, v_snd_1763_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1782_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_snd_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1780_; 
v_snd_1770_ = lean_ctor_get(v_a_1766_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_a_1766_, 0);
lean_dec(v_unused_1781_);
v___x_1772_ = v_a_1766_;
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snd_1770_);
lean_dec(v_a_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_fst_1762_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_fst_1762_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1770_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1775_);
v___x_1777_ = v___x_1768_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
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
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_fst_1762_);
v_a_1783_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1765_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1765_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_dec_ref(v_e_1735_);
return v___x_1760_;
}
}
else
{
lean_object* v_val_1791_; lean_object* v___x_1793_; 
lean_dec_ref(v_e_1735_);
lean_dec_ref(v_post_1731_);
lean_dec_ref(v_pre_1730_);
v_val_1791_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v___x_1754_, 1);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v_val_1791_);
v___x_1793_ = v___x_1752_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_val_1791_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_snd_1750_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1793_);
v___x_1795_ = v___x_1747_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_e_1735_);
lean_dec_ref(v_post_1731_);
lean_dec_ref(v_pre_1730_);
v_a_1800_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1744_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1744_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1808_, lean_object* v_post_1809_, uint8_t v_usedLetOnly_1810_, uint8_t v_skipConstInApp_1811_, uint8_t v_skipInstances_1812_, lean_object* v_fvars_1813_, lean_object* v_e_1814_, lean_object* v_a_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
if (lean_obj_tag(v_e_1814_) == 7)
{
lean_object* v_binderName_1822_; lean_object* v_binderType_1823_; lean_object* v_body_1824_; uint8_t v_binderInfo_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_binderName_1822_ = lean_ctor_get(v_e_1814_, 0);
lean_inc(v_binderName_1822_);
v_binderType_1823_ = lean_ctor_get(v_e_1814_, 1);
lean_inc_ref(v_binderType_1823_);
v_body_1824_ = lean_ctor_get(v_e_1814_, 2);
lean_inc_ref(v_body_1824_);
v_binderInfo_1825_ = lean_ctor_get_uint8(v_e_1814_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1814_, 3);
v___x_1826_ = lean_box(v_usedLetOnly_1810_);
v___x_1827_ = lean_box(v_skipConstInApp_1811_);
v___x_1828_ = lean_box(v_skipInstances_1812_);
lean_inc_ref(v_post_1809_);
lean_inc_ref(v_pre_1808_);
lean_inc_ref(v_fvars_1813_);
v___f_1829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1829_, 0, v_fvars_1813_);
lean_closure_set(v___f_1829_, 1, v_pre_1808_);
lean_closure_set(v___f_1829_, 2, v_post_1809_);
lean_closure_set(v___f_1829_, 3, v___x_1826_);
lean_closure_set(v___f_1829_, 4, v___x_1827_);
lean_closure_set(v___f_1829_, 5, v___x_1828_);
lean_closure_set(v___f_1829_, 6, v_body_1824_);
v___x_1830_ = lean_expr_instantiate_rev(v_binderType_1823_, v_fvars_1813_);
lean_dec_ref(v_fvars_1813_);
lean_dec_ref(v_binderType_1823_);
v___x_1831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1808_, v_post_1809_, v_usedLetOnly_1810_, v_skipConstInApp_1811_, v_skipInstances_1812_, v___x_1830_, v_a_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v_fst_1833_; lean_object* v_snd_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v_fst_1833_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_fst_1833_);
v_snd_1834_ = lean_ctor_get(v_a_1832_, 1);
lean_inc(v_snd_1834_);
lean_dec(v_a_1832_);
v___x_1835_ = 0;
v___x_1836_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1822_, v_binderInfo_1825_, v_fst_1833_, v___f_1829_, v___x_1835_, v_a_1815_, v_snd_1834_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1836_;
}
else
{
lean_dec_ref(v___f_1829_);
lean_dec(v_binderName_1822_);
return v___x_1831_;
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_expr_instantiate_rev(v_e_1814_, v_fvars_1813_);
lean_dec_ref(v_e_1814_);
lean_inc_ref(v_post_1809_);
lean_inc_ref(v_pre_1808_);
v___x_1838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1808_, v_post_1809_, v_usedLetOnly_1810_, v_skipConstInApp_1811_, v_skipInstances_1812_, v___x_1837_, v_a_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; uint8_t v___x_1842_; uint8_t v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v_fst_1840_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec(v_a_1839_);
v___x_1842_ = 0;
v___x_1843_ = 1;
v___x_1844_ = 1;
v___x_1845_ = l_Lean_Meta_mkForallFVars(v_fvars_1813_, v_fst_1840_, v___x_1842_, v_usedLetOnly_1810_, v___x_1843_, v___x_1844_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec_ref(v_fvars_1813_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1808_, v_post_1809_, v_usedLetOnly_1810_, v_skipConstInApp_1811_, v_skipInstances_1812_, v_a_1846_, v_a_1815_, v_snd_1841_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1847_;
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_snd_1841_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v_a_1848_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1845_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1845_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1856_, lean_object* v_pre_1857_, lean_object* v_post_1858_, uint8_t v_usedLetOnly_1859_, uint8_t v_skipConstInApp_1860_, uint8_t v_skipInstances_1861_, lean_object* v_body_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_array_push(v_fvars_1856_, v_x_1863_);
v___x_1872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1857_, v_post_1858_, v_usedLetOnly_1859_, v_skipConstInApp_1860_, v_skipInstances_1861_, v___x_1871_, v_body_1862_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1873_, lean_object* v_post_1874_, lean_object* v_usedLetOnly_1875_, lean_object* v_skipConstInApp_1876_, lean_object* v_skipInstances_1877_, lean_object* v_sz_1878_, lean_object* v_i_1879_, lean_object* v_bs_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
uint8_t v_usedLetOnly_boxed_1888_; uint8_t v_skipConstInApp_boxed_1889_; uint8_t v_skipInstances_boxed_1890_; size_t v_sz_boxed_1891_; size_t v_i_boxed_1892_; lean_object* v_res_1893_; 
v_usedLetOnly_boxed_1888_ = lean_unbox(v_usedLetOnly_1875_);
v_skipConstInApp_boxed_1889_ = lean_unbox(v_skipConstInApp_1876_);
v_skipInstances_boxed_1890_ = lean_unbox(v_skipInstances_1877_);
v_sz_boxed_1891_ = lean_unbox_usize(v_sz_1878_);
lean_dec(v_sz_1878_);
v_i_boxed_1892_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1873_, v_post_1874_, v_usedLetOnly_boxed_1888_, v_skipConstInApp_boxed_1889_, v_skipInstances_boxed_1890_, v_sz_boxed_1891_, v_i_boxed_1892_, v_bs_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1881_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1894_, lean_object* v_post_1895_, lean_object* v_usedLetOnly_1896_, lean_object* v_skipConstInApp_1897_, lean_object* v_skipInstances_1898_, lean_object* v_e_1899_, lean_object* v_a_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v_usedLetOnly_boxed_1907_; uint8_t v_skipConstInApp_boxed_1908_; uint8_t v_skipInstances_boxed_1909_; lean_object* v_res_1910_; 
v_usedLetOnly_boxed_1907_ = lean_unbox(v_usedLetOnly_1896_);
v_skipConstInApp_boxed_1908_ = lean_unbox(v_skipConstInApp_1897_);
v_skipInstances_boxed_1909_ = lean_unbox(v_skipInstances_1898_);
v_res_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1894_, v_post_1895_, v_usedLetOnly_boxed_1907_, v_skipConstInApp_boxed_1908_, v_skipInstances_boxed_1909_, v_e_1899_, v_a_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v_a_1900_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1911_, lean_object* v_post_1912_, lean_object* v_usedLetOnly_1913_, lean_object* v_skipConstInApp_1914_, lean_object* v_skipInstances_1915_, lean_object* v_fvars_1916_, lean_object* v_e_1917_, lean_object* v_a_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_usedLetOnly_boxed_1925_; uint8_t v_skipConstInApp_boxed_1926_; uint8_t v_skipInstances_boxed_1927_; lean_object* v_res_1928_; 
v_usedLetOnly_boxed_1925_ = lean_unbox(v_usedLetOnly_1913_);
v_skipConstInApp_boxed_1926_ = lean_unbox(v_skipConstInApp_1914_);
v_skipInstances_boxed_1927_ = lean_unbox(v_skipInstances_1915_);
v_res_1928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1911_, v_post_1912_, v_usedLetOnly_boxed_1925_, v_skipConstInApp_boxed_1926_, v_skipInstances_boxed_1927_, v_fvars_1916_, v_e_1917_, v_a_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v_a_1918_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1929_, lean_object* v_post_1930_, lean_object* v_usedLetOnly_1931_, lean_object* v_skipConstInApp_1932_, lean_object* v_skipInstances_1933_, lean_object* v_fvars_1934_, lean_object* v_e_1935_, lean_object* v_a_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v_usedLetOnly_boxed_1943_; uint8_t v_skipConstInApp_boxed_1944_; uint8_t v_skipInstances_boxed_1945_; lean_object* v_res_1946_; 
v_usedLetOnly_boxed_1943_ = lean_unbox(v_usedLetOnly_1931_);
v_skipConstInApp_boxed_1944_ = lean_unbox(v_skipConstInApp_1932_);
v_skipInstances_boxed_1945_ = lean_unbox(v_skipInstances_1933_);
v_res_1946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1929_, v_post_1930_, v_usedLetOnly_boxed_1943_, v_skipConstInApp_boxed_1944_, v_skipInstances_boxed_1945_, v_fvars_1934_, v_e_1935_, v_a_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v_a_1936_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1947_, lean_object* v_post_1948_, lean_object* v_usedLetOnly_1949_, lean_object* v_skipConstInApp_1950_, lean_object* v_skipInstances_1951_, lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v_usedLetOnly_boxed_1960_; uint8_t v_skipConstInApp_boxed_1961_; uint8_t v_skipInstances_boxed_1962_; lean_object* v_res_1963_; 
v_usedLetOnly_boxed_1960_ = lean_unbox(v_usedLetOnly_1949_);
v_skipConstInApp_boxed_1961_ = lean_unbox(v_skipConstInApp_1950_);
v_skipInstances_boxed_1962_ = lean_unbox(v_skipInstances_1951_);
v_res_1963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1947_, v_post_1948_, v_usedLetOnly_boxed_1960_, v_skipConstInApp_boxed_1961_, v_skipInstances_boxed_1962_, v_e_1952_, v_a_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_a_1953_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1964_, lean_object* v_post_1965_, lean_object* v_usedLetOnly_1966_, lean_object* v_skipConstInApp_1967_, lean_object* v_skipInstances_1968_, lean_object* v_fvars_1969_, lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_usedLetOnly_boxed_1978_; uint8_t v_skipConstInApp_boxed_1979_; uint8_t v_skipInstances_boxed_1980_; lean_object* v_res_1981_; 
v_usedLetOnly_boxed_1978_ = lean_unbox(v_usedLetOnly_1966_);
v_skipConstInApp_boxed_1979_ = lean_unbox(v_skipConstInApp_1967_);
v_skipInstances_boxed_1980_ = lean_unbox(v_skipInstances_1968_);
v_res_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1964_, v_post_1965_, v_usedLetOnly_boxed_1978_, v_skipConstInApp_boxed_1979_, v_skipInstances_boxed_1980_, v_fvars_1969_, v_e_1970_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v_a_1971_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_1982_, lean_object* v___x_1983_, lean_object* v_pre_1984_, lean_object* v_post_1985_, lean_object* v_usedLetOnly_1986_, lean_object* v_skipConstInApp_1987_, lean_object* v_skipInstances_1988_, lean_object* v_a_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v_usedLetOnly_boxed_1998_; uint8_t v_skipConstInApp_boxed_1999_; uint8_t v_skipInstances_boxed_2000_; lean_object* v_res_2001_; 
v_usedLetOnly_boxed_1998_ = lean_unbox(v_usedLetOnly_1986_);
v_skipConstInApp_boxed_1999_ = lean_unbox(v_skipConstInApp_1987_);
v_skipInstances_boxed_2000_ = lean_unbox(v_skipInstances_1988_);
v_res_2001_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1982_, v___x_1983_, v_pre_1984_, v_post_1985_, v_usedLetOnly_boxed_1998_, v_skipConstInApp_boxed_1999_, v_skipInstances_boxed_2000_, v_a_1989_, v_b_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1991_);
lean_dec_ref(v___x_1983_);
lean_dec(v_upperBound_1982_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2002_, lean_object* v_pre_2003_, lean_object* v_post_2004_, lean_object* v_usedLetOnly_2005_, lean_object* v_skipConstInApp_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_skipInstances_boxed_2017_; uint8_t v_usedLetOnly_boxed_2018_; uint8_t v_skipConstInApp_boxed_2019_; lean_object* v_res_2020_; 
v_skipInstances_boxed_2017_ = lean_unbox(v_skipInstances_2002_);
v_usedLetOnly_boxed_2018_ = lean_unbox(v_usedLetOnly_2005_);
v_skipConstInApp_boxed_2019_ = lean_unbox(v_skipConstInApp_2006_);
v_res_2020_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2017_, v_pre_2003_, v_post_2004_, v_usedLetOnly_boxed_2018_, v_skipConstInApp_boxed_2019_, v_x_2007_, v_x_2008_, v_x_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2010_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2021_, lean_object* v_x_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = lean_apply_1(v_x_2022_, lean_box(0));
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___y_2023_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2032_, v_x_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_unsigned_to_nat(16u);
v___x_2043_ = lean_mk_array(v___x_2042_, v___x_2041_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2048_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2048_, 0, lean_box(0));
lean_closure_set(v___x_2048_, 1, lean_box(0));
lean_closure_set(v___x_2048_, 2, v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2049_, lean_object* v_pre_2050_, lean_object* v_post_2051_, uint8_t v_usedLetOnly_2052_, uint8_t v_skipConstInApp_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_a_2063_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___x_2066_; 
v___x_2060_ = 0;
v___x_2061_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2062_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2061_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
v_fst_2064_ = lean_ctor_get(v_a_2063_, 0);
lean_inc(v_fst_2064_);
v_snd_2065_ = lean_ctor_get(v_a_2063_, 1);
lean_inc(v_snd_2065_);
lean_dec(v_a_2063_);
v___x_2066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2050_, v_post_2051_, v_usedLetOnly_2052_, v_skipConstInApp_2053_, v___x_2060_, v_input_2049_, v_fst_2064_, v_snd_2065_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2088_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v_fst_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v_a_2067_, 1);
lean_inc(v_snd_2069_);
lean_dec(v_a_2067_);
v___x_2070_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2070_, 0, lean_box(0));
lean_closure_set(v___x_2070_, 1, lean_box(0));
lean_closure_set(v___x_2070_, 2, v_fst_2064_);
v___x_2071_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2070_, v_snd_2069_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2088_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2088_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
v_snd_2076_ = lean_ctor_get(v_a_2072_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2072_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_a_2072_, 0);
lean_dec(v_unused_2087_);
v___x_2078_ = v_a_2072_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_dec(v_a_2072_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v_fst_2068_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fst_2068_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_snd_2076_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2081_);
v___x_2083_ = v___x_2074_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_dec(v_fst_2064_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2089_, lean_object* v_pre_2090_, lean_object* v_post_2091_, lean_object* v_usedLetOnly_2092_, lean_object* v_skipConstInApp_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_usedLetOnly_boxed_2100_; uint8_t v_skipConstInApp_boxed_2101_; lean_object* v_res_2102_; 
v_usedLetOnly_boxed_2100_ = lean_unbox(v_usedLetOnly_2092_);
v_skipConstInApp_boxed_2101_ = lean_unbox(v_skipConstInApp_2093_);
v_res_2102_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2089_, v_pre_2090_, v_post_2091_, v_usedLetOnly_boxed_2100_, v_skipConstInApp_boxed_2101_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___y_2112_; lean_object* v___x_2129_; uint8_t v_transparency_2130_; lean_object* v___f_2131_; lean_object* v___f_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2129_ = l_Lean_Meta_Context_config(v_a_2106_);
v_transparency_2130_ = lean_ctor_get_uint8(v___x_2129_, 9);
lean_dec_ref(v___x_2129_);
v___f_2131_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2132_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2133_ = 0;
v___x_2134_ = 3;
v___x_2135_ = lean_box(0);
v___x_2136_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2130_, v___x_2134_);
if (v___x_2136_ == 0)
{
lean_object* v_keyedConfig_2137_; uint8_t v_trackZetaDelta_2138_; lean_object* v_zetaDeltaSet_2139_; lean_object* v_lctx_2140_; lean_object* v_localInstances_2141_; lean_object* v_defEqCtx_x3f_2142_; lean_object* v_synthPendingDepth_2143_; lean_object* v_customCanUnfoldPredicate_x3f_2144_; uint8_t v_univApprox_2145_; uint8_t v_inTypeClassResolution_2146_; uint8_t v_cacheInferType_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_keyedConfig_2137_ = lean_ctor_get(v_a_2106_, 0);
v_trackZetaDelta_2138_ = lean_ctor_get_uint8(v_a_2106_, sizeof(void*)*7);
v_zetaDeltaSet_2139_ = lean_ctor_get(v_a_2106_, 1);
v_lctx_2140_ = lean_ctor_get(v_a_2106_, 2);
v_localInstances_2141_ = lean_ctor_get(v_a_2106_, 3);
v_defEqCtx_x3f_2142_ = lean_ctor_get(v_a_2106_, 4);
v_synthPendingDepth_2143_ = lean_ctor_get(v_a_2106_, 5);
v_customCanUnfoldPredicate_x3f_2144_ = lean_ctor_get(v_a_2106_, 6);
v_univApprox_2145_ = lean_ctor_get_uint8(v_a_2106_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2146_ = lean_ctor_get_uint8(v_a_2106_, sizeof(void*)*7 + 2);
v_cacheInferType_2147_ = lean_ctor_get_uint8(v_a_2106_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2137_);
v___x_2148_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2134_, v_keyedConfig_2137_);
lean_inc(v_customCanUnfoldPredicate_x3f_2144_);
lean_inc(v_synthPendingDepth_2143_);
lean_inc(v_defEqCtx_x3f_2142_);
lean_inc_ref(v_localInstances_2141_);
lean_inc_ref(v_lctx_2140_);
lean_inc(v_zetaDeltaSet_2139_);
v___x_2149_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v_zetaDeltaSet_2139_);
lean_ctor_set(v___x_2149_, 2, v_lctx_2140_);
lean_ctor_set(v___x_2149_, 3, v_localInstances_2141_);
lean_ctor_set(v___x_2149_, 4, v_defEqCtx_x3f_2142_);
lean_ctor_set(v___x_2149_, 5, v_synthPendingDepth_2143_);
lean_ctor_set(v___x_2149_, 6, v_customCanUnfoldPredicate_x3f_2144_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*7, v_trackZetaDelta_2138_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*7 + 1, v_univApprox_2145_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2146_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*7 + 3, v_cacheInferType_2147_);
v___x_2150_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2105_, v___f_2132_, v___f_2131_, v___x_2133_, v___x_2133_, v___x_2135_, v___x_2149_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec_ref_known(v___x_2149_, 7);
v___y_2112_ = v___x_2150_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2105_, v___f_2132_, v___f_2131_, v___x_2133_, v___x_2133_, v___x_2135_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
v___y_2112_ = v___x_2151_;
goto v___jp_2111_;
}
v___jp_2111_:
{
if (lean_obj_tag(v___y_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_a_2113_ = lean_ctor_get(v___y_2112_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___y_2112_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___y_2112_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___y_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___y_2112_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___y_2112_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___y_2112_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___y_2112_);
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
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Meta_expandCoe(v_e_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2159_, lean_object* v_m_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2160_, v_a_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2163_, lean_object* v_m_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2163_, v_m_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_m_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2168_, v_x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
uint8_t v_res_2174_; lean_object* v_r_2175_; 
v_res_2174_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2171_, v_x_2172_, v_x_2173_);
lean_dec_ref(v_x_2173_);
lean_dec_ref(v_x_2172_);
v_r_2175_ = lean_box(v_res_2174_);
return v_r_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2176_, lean_object* v_a_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2177_, v_x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_a_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2180_, v_a_2181_, v_x_2182_);
lean_dec(v_x_2182_);
lean_dec(v_a_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2184_, lean_object* v___x_2185_, lean_object* v_pre_2186_, lean_object* v_post_2187_, uint8_t v_usedLetOnly_2188_, uint8_t v_skipConstInApp_2189_, uint8_t v_skipInstances_2190_, lean_object* v___x_2191_, lean_object* v_inst_2192_, lean_object* v_R_2193_, lean_object* v_a_2194_, lean_object* v_b_2195_, lean_object* v_c_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2184_, v___x_2185_, v_pre_2186_, v_post_2187_, v_usedLetOnly_2188_, v_skipConstInApp_2189_, v_skipInstances_2190_, v_a_2194_, v_b_2195_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2205_ = _args[0];
lean_object* v___x_2206_ = _args[1];
lean_object* v_pre_2207_ = _args[2];
lean_object* v_post_2208_ = _args[3];
lean_object* v_usedLetOnly_2209_ = _args[4];
lean_object* v_skipConstInApp_2210_ = _args[5];
lean_object* v_skipInstances_2211_ = _args[6];
lean_object* v___x_2212_ = _args[7];
lean_object* v_inst_2213_ = _args[8];
lean_object* v_R_2214_ = _args[9];
lean_object* v_a_2215_ = _args[10];
lean_object* v_b_2216_ = _args[11];
lean_object* v_c_2217_ = _args[12];
lean_object* v___y_2218_ = _args[13];
lean_object* v___y_2219_ = _args[14];
lean_object* v___y_2220_ = _args[15];
lean_object* v___y_2221_ = _args[16];
lean_object* v___y_2222_ = _args[17];
lean_object* v___y_2223_ = _args[18];
lean_object* v___y_2224_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2225_; uint8_t v_skipConstInApp_boxed_2226_; uint8_t v_skipInstances_boxed_2227_; lean_object* v_res_2228_; 
v_usedLetOnly_boxed_2225_ = lean_unbox(v_usedLetOnly_2209_);
v_skipConstInApp_boxed_2226_ = lean_unbox(v_skipConstInApp_2210_);
v_skipInstances_boxed_2227_ = lean_unbox(v_skipInstances_2211_);
v_res_2228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2205_, v___x_2206_, v_pre_2207_, v_post_2208_, v_usedLetOnly_boxed_2225_, v_skipConstInApp_boxed_2226_, v_skipInstances_boxed_2227_, v___x_2212_, v_inst_2213_, v_R_2214_, v_a_2215_, v_b_2216_, v_c_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2218_);
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2206_);
lean_dec(v_upperBound_2205_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2229_, lean_object* v_m_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2230_, v_a_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2233_, lean_object* v_m_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2233_, v_m_2234_, v_a_2235_);
lean_dec_ref(v_a_2235_);
lean_dec_ref(v_m_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2237_, lean_object* v_name_2238_, uint8_t v_bi_2239_, lean_object* v_type_2240_, lean_object* v_k_2241_, uint8_t v_kind_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2238_, v_bi_2239_, v_type_2240_, v_k_2241_, v_kind_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_name_2252_, lean_object* v_bi_2253_, lean_object* v_type_2254_, lean_object* v_k_2255_, lean_object* v_kind_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_bi_boxed_2264_; uint8_t v_kind_boxed_2265_; lean_object* v_res_2266_; 
v_bi_boxed_2264_ = lean_unbox(v_bi_2253_);
v_kind_boxed_2265_ = lean_unbox(v_kind_2256_);
v_res_2266_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2251_, v_name_2252_, v_bi_boxed_2264_, v_type_2254_, v_k_2255_, v_kind_boxed_2265_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2257_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2267_, lean_object* v_name_2268_, lean_object* v_type_2269_, lean_object* v_val_2270_, lean_object* v_k_2271_, uint8_t v_nondep_2272_, uint8_t v_kind_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2268_, v_type_2269_, v_val_2270_, v_k_2271_, v_nondep_2272_, v_kind_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_name_2283_, lean_object* v_type_2284_, lean_object* v_val_2285_, lean_object* v_k_2286_, lean_object* v_nondep_2287_, lean_object* v_kind_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
uint8_t v_nondep_boxed_2296_; uint8_t v_kind_boxed_2297_; lean_object* v_res_2298_; 
v_nondep_boxed_2296_ = lean_unbox(v_nondep_2287_);
v_kind_boxed_2297_ = lean_unbox(v_kind_2288_);
v_res_2298_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2282_, v_name_2283_, v_type_2284_, v_val_2285_, v_k_2286_, v_nondep_boxed_2296_, v_kind_boxed_2297_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2289_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2299_, lean_object* v_ref_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2300_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_ref_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2307_, v_ref_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2325_, lean_object* v_x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2325_, v_x_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2335_, lean_object* v_m_2336_, lean_object* v_a_2337_, lean_object* v_b_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2336_, v_a_2337_, v_b_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2340_, lean_object* v_x_2341_, size_t v_x_2342_, lean_object* v_x_2343_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2341_, v_x_2342_, v_x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
size_t v_x_39019__boxed_2349_; uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_x_39019__boxed_2349_ = lean_unbox_usize(v_x_2347_);
lean_dec(v_x_2347_);
v_res_2350_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2345_, v_x_2346_, v_x_39019__boxed_2349_, v_x_2348_);
lean_dec_ref(v_x_2348_);
lean_dec_ref(v_x_2346_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2352_, lean_object* v_a_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2353_, v_x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2356_, lean_object* v_a_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2356_, v_a_2357_, v_x_2358_);
lean_dec(v_x_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2360_, lean_object* v_a_2361_, lean_object* v_x_2362_){
_start:
{
uint8_t v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2361_, v_x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_a_2365_, lean_object* v_x_2366_){
_start:
{
uint8_t v_res_2367_; lean_object* v_r_2368_; 
v_res_2367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2364_, v_a_2365_, v_x_2366_);
lean_dec(v_x_2366_);
lean_dec_ref(v_a_2365_);
v_r_2368_ = lean_box(v_res_2367_);
return v_r_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2369_, lean_object* v_data_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2372_, lean_object* v_a_2373_, lean_object* v_b_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2373_, v_b_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2377_, lean_object* v_keys_2378_, lean_object* v_vals_2379_, lean_object* v_heq_2380_, lean_object* v_i_2381_, lean_object* v_k_2382_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2378_, v_i_2381_, v_k_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_keys_2385_, lean_object* v_vals_2386_, lean_object* v_heq_2387_, lean_object* v_i_2388_, lean_object* v_k_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2384_, v_keys_2385_, v_vals_2386_, v_heq_2387_, v_i_2388_, v_k_2389_);
lean_dec_ref(v_k_2389_);
lean_dec_ref(v_vals_2386_);
lean_dec_ref(v_keys_2385_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2392_, lean_object* v_i_2393_, lean_object* v_source_2394_, lean_object* v_target_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2393_, v_source_2394_, v_target_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2401_, lean_object* v_decl_2402_, lean_object* v_ref_2403_){
_start:
{
lean_object* v_defValue_2405_; lean_object* v_descr_2406_; lean_object* v_deprecation_x3f_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_defValue_2405_ = lean_ctor_get(v_decl_2402_, 0);
v_descr_2406_ = lean_ctor_get(v_decl_2402_, 1);
v_deprecation_x3f_2407_ = lean_ctor_get(v_decl_2402_, 2);
v___x_2408_ = lean_alloc_ctor(1, 0, 1);
v___x_2409_ = lean_unbox(v_defValue_2405_);
lean_ctor_set_uint8(v___x_2408_, 0, v___x_2409_);
lean_inc(v_deprecation_x3f_2407_);
lean_inc_ref(v_descr_2406_);
lean_inc_n(v_name_2401_, 2);
v___x_2410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2410_, 0, v_name_2401_);
lean_ctor_set(v___x_2410_, 1, v_ref_2403_);
lean_ctor_set(v___x_2410_, 2, v___x_2408_);
lean_ctor_set(v___x_2410_, 3, v_descr_2406_);
lean_ctor_set(v___x_2410_, 4, v_deprecation_x3f_2407_);
v___x_2411_ = lean_register_option(v_name_2401_, v___x_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2419_; 
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v___x_2411_, 0);
lean_dec(v_unused_2420_);
v___x_2413_ = v___x_2411_;
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
else
{
lean_dec(v___x_2411_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2419_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_inc(v_defValue_2405_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_name_2401_);
lean_ctor_set(v___x_2415_, 1, v_defValue_2405_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_name_2401_);
v_a_2421_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2411_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2411_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2429_, lean_object* v_decl_2430_, lean_object* v_ref_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2429_, v_decl_2430_, v_ref_2431_);
lean_dec_ref(v_decl_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2449_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2450_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2451_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2448_, v___x_2449_, v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_ref_2460_; lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2470_; 
v_ref_2460_ = lean_ctor_get(v___y_2457_, 2);
v___x_2461_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_inc(v_ref_2460_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_ref_2460_);
lean_ctor_set(v___x_2466_, 1, v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 1);
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2493_, lean_object* v_expectedType_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2500_; 
lean_inc(v_a_2498_);
lean_inc_ref(v_a_2497_);
lean_inc(v_a_2496_);
lean_inc_ref(v_a_2495_);
lean_inc_ref(v_expr_2493_);
v___x_2500_ = lean_infer_type(v_expr_2493_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc_n(v_a_2501_, 2);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = l_Lean_Meta_getLevel(v_a_2501_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
lean_inc_ref(v_expectedType_2494_);
v___x_2504_ = l_Lean_Meta_getLevel(v_expectedType_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2507_ = lean_box(0);
v___x_2508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2505_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2503_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_inc_ref(v___x_2509_);
v___x_2510_ = l_Lean_mkConst(v___x_2506_, v___x_2509_);
v___x_2511_ = lean_unsigned_to_nat(3u);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
lean_inc(v_a_2501_);
v___x_2513_ = lean_array_push(v___x_2512_, v_a_2501_);
lean_inc_ref(v_expr_2493_);
v___x_2514_ = lean_array_push(v___x_2513_, v_expr_2493_);
lean_inc_ref(v_expectedType_2494_);
v___x_2515_ = lean_array_push(v___x_2514_, v_expectedType_2494_);
v___x_2516_ = l_Lean_mkAppN(v___x_2510_, v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = lean_box(0);
v___x_2518_ = l_Lean_Meta_trySynthInstance(v___x_2516_, v___x_2517_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2616_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2616_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2616_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
switch(lean_obj_tag(v_a_2519_))
{
case 0:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_dec_ref_known(v___x_2509_, 2);
lean_dec(v_a_2501_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v___x_2523_ = lean_box(0);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
case 1:
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2611_; 
lean_del_object(v___x_2521_);
v_a_2527_ = lean_ctor_get(v_a_2519_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2519_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2529_ = v_a_2519_;
v_isShared_2530_ = v_isSharedCheck_2611_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v_a_2519_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2611_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2531_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2532_ = l_Lean_mkConst(v___x_2531_, v___x_2509_);
v___x_2533_ = lean_unsigned_to_nat(4u);
v___x_2534_ = lean_mk_empty_array_with_capacity(v___x_2533_);
v___x_2535_ = lean_array_push(v___x_2534_, v_a_2501_);
lean_inc_ref(v_expr_2493_);
v___x_2536_ = lean_array_push(v___x_2535_, v_expr_2493_);
lean_inc_ref(v_expectedType_2494_);
v___x_2537_ = lean_array_push(v___x_2536_, v_expectedType_2494_);
v___x_2538_ = lean_array_push(v___x_2537_, v_a_2527_);
v___x_2539_ = l_Lean_mkAppN(v___x_2532_, v___x_2538_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = l_Lean_Meta_expandCoe(v___x_2539_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2602_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2602_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2602_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_fst_2552_; lean_object* v___x_2553_; 
v_fst_2552_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_a_2498_);
lean_inc_ref(v_a_2497_);
lean_inc(v_a_2496_);
lean_inc_ref(v_a_2495_);
lean_inc(v_fst_2552_);
v___x_2553_ = lean_infer_type(v_fst_2552_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
lean_inc_ref(v_expectedType_2494_);
v___x_2555_ = l_Lean_Meta_isExprDefEq(v_a_2554_, v_expectedType_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2583_; 
lean_inc(v_fst_2552_);
lean_del_object(v___x_2543_);
lean_del_object(v___x_2529_);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2584_ = lean_ctor_get(v_a_2541_, 1);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_a_2541_, 0);
lean_dec(v_unused_2585_);
v___x_2559_ = v_a_2541_;
v_isShared_2560_ = v_isSharedCheck_2583_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v_a_2541_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2583_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2561_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2562_ = l_Lean_indentExpr(v_expr_2493_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 7);
lean_ctor_set(v___x_2559_, 1, v___x_2562_);
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v___x_2565_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_indentExpr(v_expectedType_2494_);
v___x_2568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l_Lean_indentExpr(v_fst_2552_);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2572_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
goto v___jp_2545_;
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_del_object(v___x_2543_);
lean_dec(v_a_2541_);
lean_del_object(v___x_2529_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2586_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2555_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2555_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_del_object(v___x_2543_);
lean_dec(v_a_2541_);
lean_del_object(v___x_2529_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2594_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2553_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2553_);
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
v___jp_2545_:
{
lean_object* v___x_2547_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_a_2541_);
v___x_2547_ = v___x_2529_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2541_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2547_);
v___x_2549_ = v___x_2543_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2529_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2603_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2540_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2540_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
default: 
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2509_, 2);
lean_dec(v_a_2501_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v___x_2612_ = lean_box(2);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2612_);
v___x_2614_ = v___x_2521_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref_known(v___x_2509_, 2);
lean_dec(v_a_2501_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2617_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2518_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2518_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
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
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2501_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2625_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2504_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2504_);
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
lean_dec(v_a_2501_);
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2633_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2502_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2502_);
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
lean_dec_ref(v_expectedType_2494_);
lean_dec_ref(v_expr_2493_);
v_a_2641_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2500_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2500_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2649_, lean_object* v_expectedType_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2649_, v_expectedType_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2657_, lean_object* v_msg_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2665_, v_msg_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2673_, lean_object* v_expectedType_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2673_, v_expectedType_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2705_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2705_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
switch(lean_obj_tag(v_a_2681_))
{
case 0:
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2685_ = lean_box(0);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2685_);
v___x_2687_ = v___x_2683_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
case 1:
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2700_; 
v_a_2689_ = lean_ctor_get(v_a_2681_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_a_2681_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2691_ = v_a_2681_;
v_isShared_2692_ = v_isSharedCheck_2700_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v_a_2681_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2700_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_fst_2693_; lean_object* v___x_2695_; 
v_fst_2693_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_fst_2693_);
lean_dec(v_a_2689_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v_fst_2693_);
v___x_2695_ = v___x_2691_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_fst_2693_);
v___x_2695_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2697_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2695_);
v___x_2697_ = v___x_2683_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
default: 
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_box(2);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2701_);
v___x_2703_ = v___x_2683_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
v_a_2706_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2680_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2680_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2714_, lean_object* v_expectedType_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2714_, v_expectedType_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2721_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2730_ = l_Lean_stringToMessageData(v___x_2729_);
return v___x_2730_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2733_ = l_Lean_stringToMessageData(v___x_2732_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2736_ = l_Lean_stringToMessageData(v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___x_2743_; 
lean_inc(v_a_2741_);
lean_inc_ref(v_a_2740_);
lean_inc(v_a_2739_);
lean_inc_ref(v_a_2738_);
lean_inc_ref(v_expr_2737_);
v___x_2743_ = lean_infer_type(v_expr_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_n(v_a_2744_, 2);
lean_dec_ref_known(v___x_2743_, 1);
v___x_2745_ = l_Lean_Meta_getLevel(v_a_2744_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc_n(v_a_2748_, 2);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = l_Lean_mkSort(v_a_2748_);
lean_inc(v_a_2744_);
v___x_2750_ = l_Lean_mkArrow(v_a_2744_, v___x_2749_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2751_);
v___x_2753_ = 0;
v___x_2754_ = lean_box(0);
v___x_2755_ = l_Lean_Meta_mkFreshExprMVar(v___x_2752_, v___x_2753_, v___x_2754_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_n(v_a_2756_, 2);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2758_ = lean_box(0);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2748_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2746_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
lean_inc_ref(v___x_2760_);
v___x_2761_ = l_Lean_Expr_const___override(v___x_2757_, v___x_2760_);
lean_inc(v_a_2744_);
v___x_2762_ = l_Lean_mkAppB(v___x_2761_, v_a_2744_, v_a_2756_);
v___x_2763_ = lean_box(0);
v___x_2764_ = l_Lean_Meta_trySynthInstance(v___x_2762_, v___x_2763_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2851_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2851_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2851_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
if (lean_obj_tag(v_a_2765_) == 1)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2847_; 
lean_del_object(v___x_2767_);
v_a_2769_ = lean_ctor_get(v_a_2765_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_a_2765_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2771_ = v_a_2765_;
v_isShared_2772_ = v_isSharedCheck_2847_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v_a_2765_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2847_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2773_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2774_ = l_Lean_Expr_const___override(v___x_2773_, v___x_2760_);
lean_inc_ref(v_expr_2737_);
lean_inc(v_a_2769_);
v___x_2775_ = l_Lean_mkApp4(v___x_2774_, v_a_2744_, v_a_2756_, v_a_2769_, v_expr_2737_);
v___x_2776_ = l_Lean_Meta_expandCoe(v___x_2775_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2838_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2838_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2838_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_fst_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2836_; 
v_fst_2781_ = lean_ctor_get(v_a_2777_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2777_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v_a_2777_, 1);
lean_dec(v_unused_2837_);
v___x_2783_ = v_a_2777_;
v_isShared_2784_ = v_isSharedCheck_2836_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_fst_2781_);
lean_dec(v_a_2777_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2836_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2792_; 
lean_inc(v_a_2741_);
lean_inc_ref(v_a_2740_);
lean_inc(v_a_2739_);
lean_inc_ref(v_a_2738_);
lean_inc(v_fst_2781_);
v___x_2792_ = lean_infer_type(v_fst_2781_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
lean_inc(v_a_2741_);
lean_inc_ref(v_a_2740_);
lean_inc(v_a_2739_);
lean_inc_ref(v_a_2738_);
v___x_2794_ = lean_whnf(v_a_2793_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; uint8_t v___x_2796_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = l_Lean_Expr_isForall(v_a_2795_);
lean_dec(v_a_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_del_object(v___x_2779_);
lean_del_object(v___x_2771_);
v___x_2797_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2798_ = l_Lean_indentExpr(v_expr_2737_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 7);
lean_ctor_set(v___x_2783_, 1, v___x_2798_);
lean_ctor_set(v___x_2783_, 0, v___x_2797_);
v___x_2800_ = v___x_2783_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v___x_2801_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = l_Lean_indentExpr(v_fst_2781_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2806_ = l_Lean_indentExpr(v_a_2769_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_MessageData_hint_x27(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2804_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2809_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_del_object(v___x_2783_);
lean_dec(v_a_2769_);
lean_dec_ref(v_expr_2737_);
goto v___jp_2785_;
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2779_);
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_expr_2737_);
v_a_2820_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2794_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2794_);
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
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2779_);
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_expr_2737_);
v_a_2828_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2792_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2792_);
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
v___jp_2785_:
{
lean_object* v___x_2787_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v_fst_2781_);
v___x_2787_ = v___x_2771_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_fst_2781_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2787_);
v___x_2789_ = v___x_2779_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_del_object(v___x_2771_);
lean_dec(v_a_2769_);
lean_dec_ref(v_expr_2737_);
v_a_2839_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2776_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2776_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
else
{
lean_object* v___x_2849_; 
lean_dec(v_a_2765_);
lean_dec_ref_known(v___x_2760_, 2);
lean_dec(v_a_2756_);
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2763_);
v___x_2849_ = v___x_2767_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2763_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref_known(v___x_2760_, 2);
lean_dec(v_a_2756_);
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
v_a_2852_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2764_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2764_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
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
lean_dec(v_a_2748_);
lean_dec(v_a_2746_);
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
v_a_2860_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2755_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2755_);
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
lean_dec(v_a_2748_);
lean_dec(v_a_2746_);
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
v_a_2868_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2750_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2750_);
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
lean_dec(v_a_2746_);
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
v_a_2876_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2747_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2747_);
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
lean_dec(v_a_2744_);
lean_dec_ref(v_expr_2737_);
v_a_2884_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2745_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2745_);
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
lean_dec_ref(v_expr_2737_);
v_a_2892_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2743_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2743_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2906_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2918_ = l_Lean_stringToMessageData(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; 
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc_ref(v_expr_2919_);
v___x_2925_ = lean_infer_type(v_expr_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc_n(v_a_2926_, 2);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = l_Lean_Meta_getLevel(v_a_2926_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc_n(v_a_2930_, 2);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = l_Lean_mkSort(v_a_2930_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
v___x_2933_ = 0;
v___x_2934_ = lean_box(0);
v___x_2935_ = l_Lean_Meta_mkFreshExprMVar(v___x_2932_, v___x_2933_, v___x_2934_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_n(v_a_2936_, 2);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2930_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_a_2928_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
lean_inc_ref(v___x_2940_);
v___x_2941_ = l_Lean_Expr_const___override(v___x_2937_, v___x_2940_);
lean_inc(v_a_2926_);
v___x_2942_ = l_Lean_mkAppB(v___x_2941_, v_a_2926_, v_a_2936_);
v___x_2943_ = lean_box(0);
v___x_2944_ = l_Lean_Meta_trySynthInstance(v___x_2942_, v___x_2943_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3031_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3031_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3031_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_a_2945_) == 1)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3027_; 
lean_del_object(v___x_2947_);
v_a_2949_ = lean_ctor_get(v_a_2945_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2951_ = v_a_2945_;
v_isShared_2952_ = v_isSharedCheck_3027_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v_a_2945_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3027_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2953_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2954_ = l_Lean_Expr_const___override(v___x_2953_, v___x_2940_);
lean_inc_ref(v_expr_2919_);
lean_inc(v_a_2949_);
v___x_2955_ = l_Lean_mkApp4(v___x_2954_, v_a_2926_, v_a_2936_, v_a_2949_, v_expr_2919_);
v___x_2956_ = l_Lean_Meta_expandCoe(v___x_2955_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3018_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_3018_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3018_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_fst_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3016_; 
v_fst_2961_ = lean_ctor_get(v_a_2957_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v_a_2957_, 1);
lean_dec(v_unused_3017_);
v___x_2963_ = v_a_2957_;
v_isShared_2964_ = v_isSharedCheck_3016_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_fst_2961_);
lean_dec(v_a_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3016_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2972_; 
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
lean_inc(v_fst_2961_);
v___x_2972_ = lean_infer_type(v_fst_2961_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
lean_inc(v_a_2921_);
lean_inc_ref(v_a_2920_);
v___x_2974_ = lean_whnf(v_a_2973_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; uint8_t v___x_2976_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = l_Lean_Expr_isSort(v_a_2975_);
lean_dec(v_a_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_del_object(v___x_2959_);
lean_del_object(v___x_2951_);
v___x_2977_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2978_ = l_Lean_indentExpr(v_expr_2919_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 7);
lean_ctor_set(v___x_2963_, 1, v___x_2978_);
lean_ctor_set(v___x_2963_, 0, v___x_2977_);
v___x_2980_ = v___x_2963_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v___x_2981_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_indentExpr(v_fst_2961_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_2986_ = l_Lean_indentExpr(v_a_2949_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = l_Lean_MessageData_hint_x27(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2984_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2989_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_del_object(v___x_2963_);
lean_dec(v_a_2949_);
lean_dec_ref(v_expr_2919_);
goto v___jp_2965_;
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_del_object(v___x_2963_);
lean_dec(v_fst_2961_);
lean_del_object(v___x_2959_);
lean_del_object(v___x_2951_);
lean_dec(v_a_2949_);
lean_dec_ref(v_expr_2919_);
v_a_3000_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2974_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2974_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_del_object(v___x_2963_);
lean_dec(v_fst_2961_);
lean_del_object(v___x_2959_);
lean_del_object(v___x_2951_);
lean_dec(v_a_2949_);
lean_dec_ref(v_expr_2919_);
v_a_3008_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2972_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2972_);
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
v___jp_2965_:
{
lean_object* v___x_2967_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v_fst_2961_);
v___x_2967_ = v___x_2951_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_fst_2961_);
v___x_2967_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2967_);
v___x_2969_ = v___x_2959_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2951_);
lean_dec(v_a_2949_);
lean_dec_ref(v_expr_2919_);
v_a_3019_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2956_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2956_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_a_2945_);
lean_dec_ref_known(v___x_2940_, 2);
lean_dec(v_a_2936_);
lean_dec(v_a_2926_);
lean_dec_ref(v_expr_2919_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2943_);
v___x_3029_ = v___x_2947_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_2943_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref_known(v___x_2940_, 2);
lean_dec(v_a_2936_);
lean_dec(v_a_2926_);
lean_dec_ref(v_expr_2919_);
v_a_3032_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2944_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2944_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
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
lean_dec(v_a_2930_);
lean_dec(v_a_2928_);
lean_dec(v_a_2926_);
lean_dec_ref(v_expr_2919_);
v_a_3040_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2935_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2935_);
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
lean_dec(v_a_2928_);
lean_dec(v_a_2926_);
lean_dec_ref(v_expr_2919_);
v_a_3048_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2929_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2929_);
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
lean_dec(v_a_2926_);
lean_dec_ref(v_expr_2919_);
v_a_3056_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2927_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2927_);
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
lean_dec_ref(v_expr_2919_);
v_a_3064_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2925_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2925_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = l_Lean_Expr_hasMVar(v_e_3079_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v_e_3079_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v_mctx_3085_; lean_object* v___x_3086_; lean_object* v_fst_3087_; lean_object* v_snd_3088_; lean_object* v___x_3089_; lean_object* v_cache_3090_; lean_object* v_zetaDeltaFVarIds_3091_; lean_object* v_postponed_3092_; lean_object* v_diag_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3102_; 
v___x_3084_ = lean_st_ref_get(v___y_3080_);
v_mctx_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_ref(v_mctx_3085_);
lean_dec(v___x_3084_);
v___x_3086_ = l_Lean_instantiateMVarsCore(v_mctx_3085_, v_e_3079_);
v_fst_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_fst_3087_);
v_snd_3088_ = lean_ctor_get(v___x_3086_, 1);
lean_inc(v_snd_3088_);
lean_dec_ref(v___x_3086_);
v___x_3089_ = lean_st_ref_take(v___y_3080_);
v_cache_3090_ = lean_ctor_get(v___x_3089_, 1);
v_zetaDeltaFVarIds_3091_ = lean_ctor_get(v___x_3089_, 2);
v_postponed_3092_ = lean_ctor_get(v___x_3089_, 3);
v_diag_3093_ = lean_ctor_get(v___x_3089_, 4);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3089_, 0);
lean_dec(v_unused_3103_);
v___x_3095_ = v___x_3089_;
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_diag_3093_);
lean_inc(v_postponed_3092_);
lean_inc(v_zetaDeltaFVarIds_3091_);
lean_inc(v_cache_3090_);
lean_dec(v___x_3089_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3102_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v_snd_3088_);
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_snd_3088_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_cache_3090_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_zetaDeltaFVarIds_3091_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_postponed_3092_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v_diag_3093_);
v___x_3098_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_st_ref_put(v___y_3080_, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_fst_3087_);
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3104_, v___y_3105_);
lean_dec(v___y_3105_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3108_, v___y_3110_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___y_3129_; lean_object* v___x_3168_; uint8_t v_transparency_3169_; uint8_t v___x_3170_; uint8_t v___x_3171_; 
v___x_3168_ = l_Lean_Meta_Context_config(v_a_3123_);
v_transparency_3169_ = lean_ctor_get_uint8(v___x_3168_, 9);
lean_dec_ref(v___x_3168_);
v___x_3170_ = 2;
v___x_3171_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3169_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v_keyedConfig_3172_; uint8_t v_trackZetaDelta_3173_; lean_object* v_zetaDeltaSet_3174_; lean_object* v_lctx_3175_; lean_object* v_localInstances_3176_; lean_object* v_defEqCtx_x3f_3177_; lean_object* v_synthPendingDepth_3178_; lean_object* v_customCanUnfoldPredicate_x3f_3179_; uint8_t v_univApprox_3180_; uint8_t v_inTypeClassResolution_3181_; uint8_t v_cacheInferType_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_keyedConfig_3172_ = lean_ctor_get(v_a_3123_, 0);
v_trackZetaDelta_3173_ = lean_ctor_get_uint8(v_a_3123_, sizeof(void*)*7);
v_zetaDeltaSet_3174_ = lean_ctor_get(v_a_3123_, 1);
v_lctx_3175_ = lean_ctor_get(v_a_3123_, 2);
v_localInstances_3176_ = lean_ctor_get(v_a_3123_, 3);
v_defEqCtx_x3f_3177_ = lean_ctor_get(v_a_3123_, 4);
v_synthPendingDepth_3178_ = lean_ctor_get(v_a_3123_, 5);
v_customCanUnfoldPredicate_x3f_3179_ = lean_ctor_get(v_a_3123_, 6);
v_univApprox_3180_ = lean_ctor_get_uint8(v_a_3123_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3181_ = lean_ctor_get_uint8(v_a_3123_, sizeof(void*)*7 + 2);
v_cacheInferType_3182_ = lean_ctor_get_uint8(v_a_3123_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3172_);
v___x_3183_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3170_, v_keyedConfig_3172_);
lean_inc(v_customCanUnfoldPredicate_x3f_3179_);
lean_inc(v_synthPendingDepth_3178_);
lean_inc(v_defEqCtx_x3f_3177_);
lean_inc_ref(v_localInstances_3176_);
lean_inc_ref(v_lctx_3175_);
lean_inc(v_zetaDeltaSet_3174_);
v___x_3184_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v_zetaDeltaSet_3174_);
lean_ctor_set(v___x_3184_, 2, v_lctx_3175_);
lean_ctor_set(v___x_3184_, 3, v_localInstances_3176_);
lean_ctor_set(v___x_3184_, 4, v_defEqCtx_x3f_3177_);
lean_ctor_set(v___x_3184_, 5, v_synthPendingDepth_3178_);
lean_ctor_set(v___x_3184_, 6, v_customCanUnfoldPredicate_x3f_3179_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*7, v_trackZetaDelta_3173_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*7 + 1, v_univApprox_3180_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3181_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*7 + 3, v_cacheInferType_3182_);
lean_inc(v_a_3126_);
lean_inc_ref(v_a_3125_);
lean_inc(v_a_3124_);
v___x_3185_ = lean_whnf(v_type_3122_, v___x_3184_, v_a_3124_, v_a_3125_, v_a_3126_);
v___y_3129_ = v___x_3185_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3186_; 
lean_inc(v_a_3126_);
lean_inc_ref(v_a_3125_);
lean_inc(v_a_3124_);
lean_inc_ref(v_a_3123_);
v___x_3186_ = lean_whnf(v_type_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
v___y_3129_ = v___x_3186_;
goto v___jp_3128_;
}
v___jp_3128_:
{
if (lean_obj_tag(v___y_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3159_; 
v_a_3130_ = lean_ctor_get(v___y_3129_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___y_3129_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3132_ = v___y_3129_;
v_isShared_3133_ = v_isSharedCheck_3159_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___y_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3159_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
if (lean_obj_tag(v_a_3130_) == 5)
{
lean_object* v_fn_3134_; lean_object* v_arg_3135_; lean_object* v___x_3136_; lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_3132_);
v_fn_3134_ = lean_ctor_get(v_a_3130_, 0);
lean_inc_ref(v_fn_3134_);
v_arg_3135_ = lean_ctor_get(v_a_3130_, 1);
lean_inc_ref(v_arg_3135_);
lean_dec_ref_known(v_a_3130_, 2);
v___x_3136_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3134_, v_a_3124_);
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3154_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3154_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3153_; 
v___x_3141_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3135_, v_a_3124_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3153_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3153_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v_a_3137_);
lean_ctor_set(v___x_3146_, 1, v_a_3142_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 1);
lean_ctor_set(v___x_3139_, 0, v___x_3146_);
v___x_3148_ = v___x_3139_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3150_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3148_);
v___x_3150_ = v___x_3144_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
lean_dec(v_a_3130_);
v___x_3155_ = lean_box(0);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3155_);
v___x_3157_ = v___x_3132_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___y_3129_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___y_3129_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___y_3129_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___y_3129_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_isTypeApp_x3f(v_type_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_isTypeApp_x3f(v_type_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3236_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
if (lean_obj_tag(v_a_3201_) == 1)
{
lean_object* v_val_3205_; lean_object* v_fst_3206_; lean_object* v___x_3207_; 
lean_del_object(v___x_3203_);
v_val_3205_ = lean_ctor_get(v_a_3201_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_a_3201_, 1);
v_fst_3206_ = lean_ctor_get(v_val_3205_, 0);
lean_inc(v_fst_3206_);
lean_dec(v_val_3205_);
v___x_3207_ = l_Lean_Meta_isMonad_x3f(v_fst_3206_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3222_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
if (lean_obj_tag(v_a_3208_) == 0)
{
uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3212_ = 0;
v___x_3213_ = lean_box(v___x_3212_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3213_);
v___x_3215_ = v___x_3210_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
else
{
uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_dec_ref_known(v_a_3208_, 1);
v___x_3217_ = 1;
v___x_3218_ = lean_box(v___x_3217_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3218_);
v___x_3220_ = v___x_3210_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
v_a_3223_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3207_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3207_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
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
uint8_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_dec(v_a_3201_);
v___x_3231_ = 0;
v___x_3232_ = lean_box(v___x_3231_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3232_);
v___x_3234_ = v___x_3203_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
v_a_3237_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3200_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3200_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Meta_isMonadApp(v_type_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3251_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3252_, lean_object* v_opt_3253_){
_start:
{
lean_object* v_name_3254_; lean_object* v_defValue_3255_; lean_object* v_map_3256_; lean_object* v___x_3257_; 
v_name_3254_ = lean_ctor_get(v_opt_3253_, 0);
v_defValue_3255_ = lean_ctor_get(v_opt_3253_, 1);
v_map_3256_ = lean_ctor_get(v_opts_3252_, 0);
v___x_3257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3256_, v_name_3254_);
if (lean_obj_tag(v___x_3257_) == 0)
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_unbox(v_defValue_3255_);
return v___x_3258_;
}
else
{
lean_object* v_val_3259_; 
v_val_3259_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v___x_3257_, 1);
if (lean_obj_tag(v_val_3259_) == 1)
{
uint8_t v_v_3260_; 
v_v_3260_ = lean_ctor_get_uint8(v_val_3259_, 0);
lean_dec_ref_known(v_val_3259_, 0);
return v_v_3260_;
}
else
{
uint8_t v___x_3261_; 
lean_dec(v_val_3259_);
v___x_3261_ = lean_unbox(v_defValue_3255_);
return v___x_3261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3262_, lean_object* v_opt_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3262_, v_opt_3263_);
lean_dec_ref(v_opt_3263_);
lean_dec_ref(v_opts_3262_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_x_3276_);
return v_res_3282_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = l_Lean_mkBVar(v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3305_, lean_object* v_expectedType_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v_a_3319_; lean_object* v___y_3323_; lean_object* v___x_3333_; lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3738_; 
v___x_3333_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3306_, v_a_3308_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3738_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3738_;
goto v_resetjp_3335_;
}
v___jp_3312_:
{
if (v___y_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___y_3313_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___y_3313_);
return v___x_3317_;
}
}
v___jp_3318_:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Lean_Exception_isInterrupt(v_a_3319_);
if (v___x_3320_ == 0)
{
uint8_t v___x_3321_; 
lean_inc_ref(v_a_3319_);
v___x_3321_ = l_Lean_Exception_isRuntime(v_a_3319_);
v___y_3313_ = v_a_3319_;
v___y_3314_ = v___x_3321_;
goto v___jp_3312_;
}
else
{
v___y_3313_ = v_a_3319_;
v___y_3314_ = v___x_3320_;
goto v___jp_3312_;
}
}
v___jp_3322_:
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3332_; 
v_a_3324_ = lean_ctor_get(v___y_3323_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___y_3323_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3326_ = v___y_3323_;
v_isShared_3327_ = v_isSharedCheck_3332_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___y_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3332_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_a_3328_; lean_object* v___x_3330_; 
v_a_3328_ = lean_ctor_get(v_a_3324_, 0);
lean_inc(v_a_3328_);
lean_dec(v_a_3324_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v_a_3328_);
v___x_3330_ = v___x_3326_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3328_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; 
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc_ref(v_e_3305_);
v___x_3338_ = lean_infer_type(v_e_3305_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3729_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3339_, v_a_3308_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3729_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3729_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; 
lean_inc(v_a_3334_);
v___x_3345_ = l_Lean_Meta_isTypeApp_x3f(v_a_3334_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3720_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3720_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3720_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
if (lean_obj_tag(v_a_3346_) == 1)
{
lean_object* v_val_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3715_; 
lean_del_object(v___x_3348_);
v_val_3350_ = lean_ctor_get(v_a_3346_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v_a_3346_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3352_ = v_a_3346_;
v_isShared_3353_ = v_isSharedCheck_3715_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_val_3350_);
lean_dec(v_a_3346_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3715_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_fst_3354_; lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3714_; 
v_fst_3354_ = lean_ctor_get(v_val_3350_, 0);
v_snd_3355_ = lean_ctor_get(v_val_3350_, 1);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_val_3350_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3357_ = v_val_3350_;
v_isShared_3358_ = v_isSharedCheck_3714_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_inc(v_fst_3354_);
lean_dec(v_val_3350_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3714_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; 
lean_inc(v_a_3341_);
v___x_3359_ = l_Lean_Meta_isTypeApp_x3f(v_a_3341_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3705_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3705_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3705_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
if (lean_obj_tag(v_a_3360_) == 1)
{
lean_object* v_val_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3700_; 
lean_del_object(v___x_3362_);
v_val_3364_ = lean_ctor_get(v_a_3360_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_a_3360_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3366_ = v_a_3360_;
v_isShared_3367_ = v_isSharedCheck_3700_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_val_3364_);
lean_dec(v_a_3360_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3700_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3699_; 
v_fst_3368_ = lean_ctor_get(v_val_3364_, 0);
v_snd_3369_ = lean_ctor_get(v_val_3364_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_val_3364_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3371_ = v_val_3364_;
v_isShared_3372_ = v_isSharedCheck_3699_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3369_);
lean_inc(v_fst_3368_);
lean_dec(v_val_3364_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3699_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_saveState___redArg(v_a_3308_, v_a_3310_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
lean_inc(v_fst_3354_);
lean_inc(v_fst_3368_);
v___x_3375_ = l_Lean_Meta_isExprDefEq(v_fst_3368_, v_fst_3354_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3682_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3682_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3682_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_unbox(v_a_3376_);
lean_dec(v_a_3376_);
if (v___x_3380_ == 0)
{
lean_object* v_toCold_3381_; lean_object* v_options_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
lean_dec(v_a_3374_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_del_object(v___x_3336_);
v_toCold_3381_ = lean_ctor_get(v_a_3309_, 0);
v_options_3382_ = lean_ctor_get(v_toCold_3381_, 2);
v___x_3383_ = l_Lean_Meta_autoLift;
v___x_3384_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3385_ = lean_box(0);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3385_);
v___x_3387_ = v___x_3378_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
else
{
lean_object* v___x_3389_; 
lean_del_object(v___x_3378_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc(v_fst_3368_);
v___x_3389_ = lean_infer_type(v_fst_3368_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
v___x_3391_ = lean_whnf(v_a_3390_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
if (lean_obj_tag(v_a_3392_) == 7)
{
lean_object* v_binderType_3393_; 
v_binderType_3393_ = lean_ctor_get(v_a_3392_, 1);
if (lean_obj_tag(v_binderType_3393_) == 3)
{
lean_object* v_body_3394_; 
v_body_3394_ = lean_ctor_get(v_a_3392_, 2);
if (lean_obj_tag(v_body_3394_) == 3)
{
lean_object* v_u_3395_; lean_object* v_u_3396_; lean_object* v___x_3397_; 
lean_inc_ref(v_body_3394_);
lean_inc_ref(v_binderType_3393_);
lean_dec_ref_known(v_a_3392_, 3);
v_u_3395_ = lean_ctor_get(v_binderType_3393_, 0);
lean_inc(v_u_3395_);
lean_dec_ref_known(v_binderType_3393_, 1);
v_u_3396_ = lean_ctor_get(v_body_3394_, 0);
lean_inc(v_u_3396_);
lean_dec_ref_known(v_body_3394_, 1);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc(v_fst_3354_);
v___x_3397_ = lean_infer_type(v_fst_3354_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
v___x_3399_ = lean_whnf(v_a_3398_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
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
v___x_3405_ = l_Lean_Meta_decLevel(v_u_3395_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = l_Lean_Meta_decLevel(v_u_3403_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
lean_inc(v_a_3406_);
v___x_3409_ = l_Lean_Meta_isLevelDefEq(v_a_3406_, v_a_3408_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3574_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3574_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3574_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
uint8_t v___x_3414_; 
v___x_3414_ = lean_unbox(v_a_3410_);
lean_dec(v_a_3410_);
if (v___x_3414_ == 1)
{
lean_object* v___x_3415_; 
lean_del_object(v___x_3412_);
v___x_3415_ = l_Lean_Meta_decLevel(v_u_3396_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = l_Lean_Meta_decLevel(v_u_3404_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3420_ = lean_box(0);
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
lean_ctor_set(v___x_3371_, 1, v___x_3420_);
lean_ctor_set(v___x_3371_, 0, v_a_3418_);
v___x_3422_ = v___x_3371_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3418_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 1);
lean_ctor_set(v___x_3357_, 1, v___x_3422_);
lean_ctor_set(v___x_3357_, 0, v_a_3416_);
v___x_3424_ = v___x_3357_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3416_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v_a_3406_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_Expr_const___override(v___x_3419_, v___x_3425_);
v___x_3427_ = lean_unsigned_to_nat(2u);
v___x_3428_ = lean_mk_empty_array_with_capacity(v___x_3427_);
lean_inc(v_fst_3368_);
v___x_3429_ = lean_array_push(v___x_3428_, v_fst_3368_);
lean_inc(v_fst_3354_);
v___x_3430_ = lean_array_push(v___x_3429_, v_fst_3354_);
v___x_3431_ = l_Lean_mkAppN(v___x_3426_, v___x_3430_);
lean_dec_ref(v___x_3430_);
v___x_3432_ = lean_box(0);
v___x_3433_ = l_Lean_Meta_trySynthInstance(v___x_3431_, v___x_3432_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3564_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3564_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3564_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
if (lean_obj_tag(v_a_3434_) == 1)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
lean_del_object(v___x_3436_);
v_a_3438_ = lean_ctor_get(v_a_3434_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v_a_3434_, 1);
lean_inc(v_snd_3369_);
v___x_3439_ = l_Lean_Meta_getDecLevel(v_snd_3369_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = l_Lean_Meta_getDecLevel(v_a_3341_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
lean_inc(v_a_3334_);
v___x_3443_ = l_Lean_Meta_getDecLevel(v_a_3334_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v___x_3445_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_a_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3420_);
v___x_3447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_a_3442_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_a_3440_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
lean_inc_ref(v___x_3448_);
v___x_3449_ = l_Lean_mkConst(v___x_3445_, v___x_3448_);
v___x_3450_ = lean_unsigned_to_nat(5u);
v___x_3451_ = lean_mk_empty_array_with_capacity(v___x_3450_);
lean_inc(v_fst_3368_);
v___x_3452_ = lean_array_push(v___x_3451_, v_fst_3368_);
lean_inc(v_fst_3354_);
v___x_3453_ = lean_array_push(v___x_3452_, v_fst_3354_);
lean_inc(v_a_3438_);
v___x_3454_ = lean_array_push(v___x_3453_, v_a_3438_);
lean_inc(v_snd_3369_);
v___x_3455_ = lean_array_push(v___x_3454_, v_snd_3369_);
lean_inc_ref(v_e_3305_);
v___x_3456_ = lean_array_push(v___x_3455_, v_e_3305_);
v___x_3457_ = l_Lean_mkAppN(v___x_3449_, v___x_3456_);
lean_dec_ref(v___x_3456_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc_ref(v___x_3457_);
v___x_3458_ = lean_infer_type(v___x_3457_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
lean_inc(v_a_3334_);
v___x_3460_ = l_Lean_Meta_isExprDefEq(v_a_3334_, v_a_3459_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3555_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3555_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3555_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_unbox(v_a_3461_);
lean_dec(v_a_3461_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; 
lean_del_object(v___x_3463_);
lean_dec_ref(v___x_3457_);
lean_del_object(v___x_3366_);
lean_inc(v_fst_3354_);
v___x_3466_ = l_Lean_Meta_isMonad_x3f(v_fst_3354_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3547_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3547_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3547_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
if (lean_obj_tag(v_a_3467_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3543_; 
lean_del_object(v___x_3469_);
v_val_3471_ = lean_ctor_get(v_a_3467_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3473_ = v_a_3467_;
v_isShared_3474_ = v_isSharedCheck_3543_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_val_3471_);
lean_dec(v_a_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3543_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; 
lean_inc(v_snd_3369_);
v___x_3475_ = l_Lean_Meta_getLevel(v_snd_3369_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
lean_inc(v_snd_3355_);
v___x_3477_ = l_Lean_Meta_getLevel(v_snd_3355_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3480_ = 0;
v___x_3481_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3482_, 0, v_a_3478_);
lean_ctor_set(v___x_3482_, 1, v___x_3420_);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_a_3476_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_mkConst(v___x_3481_, v___x_3483_);
v___x_3485_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3486_ = lean_unsigned_to_nat(3u);
v___x_3487_ = lean_mk_empty_array_with_capacity(v___x_3486_);
lean_inc_n(v_snd_3369_, 2);
v___x_3488_ = lean_array_push(v___x_3487_, v_snd_3369_);
v___x_3489_ = lean_array_push(v___x_3488_, v___x_3485_);
lean_inc(v_snd_3355_);
v___x_3490_ = lean_array_push(v___x_3489_, v_snd_3355_);
v___x_3491_ = l_Lean_mkAppN(v___x_3484_, v___x_3490_);
lean_dec_ref(v___x_3490_);
v___x_3492_ = l_Lean_mkForall(v___x_3479_, v___x_3480_, v_snd_3369_, v___x_3491_);
v___x_3493_ = l_Lean_Meta_trySynthInstance(v___x_3492_, v___x_3432_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3539_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3539_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3539_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_del_object(v___x_3496_);
v_a_3498_ = lean_ctor_get(v_a_3494_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v_a_3494_, 1);
v___x_3499_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3500_ = l_Lean_mkConst(v___x_3499_, v___x_3448_);
v___x_3501_ = lean_unsigned_to_nat(8u);
v___x_3502_ = lean_mk_empty_array_with_capacity(v___x_3501_);
v___x_3503_ = lean_array_push(v___x_3502_, v_fst_3368_);
v___x_3504_ = lean_array_push(v___x_3503_, v_fst_3354_);
v___x_3505_ = lean_array_push(v___x_3504_, v_snd_3369_);
v___x_3506_ = lean_array_push(v___x_3505_, v_snd_3355_);
v___x_3507_ = lean_array_push(v___x_3506_, v_a_3438_);
v___x_3508_ = lean_array_push(v___x_3507_, v_a_3498_);
v___x_3509_ = lean_array_push(v___x_3508_, v_val_3471_);
v___x_3510_ = lean_array_push(v___x_3509_, v_e_3305_);
v___x_3511_ = l_Lean_mkAppN(v___x_3500_, v___x_3510_);
lean_dec_ref(v___x_3510_);
v___x_3512_ = l_Lean_Meta_expandCoe(v___x_3511_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_fst_3514_; lean_object* v___x_3515_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v_fst_3514_ = lean_ctor_get(v_a_3513_, 0);
lean_inc_n(v_fst_3514_, 2);
lean_dec(v_a_3513_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
v___x_3515_ = lean_infer_type(v_fst_3514_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_Meta_isExprDefEq(v_a_3334_, v_a_3516_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3532_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
uint8_t v___x_3522_; 
v___x_3522_ = lean_unbox(v_a_3518_);
lean_dec(v_a_3518_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v_fst_3514_);
lean_del_object(v___x_3473_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3432_);
v___x_3524_ = v___x_3520_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3432_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
else
{
lean_object* v___x_3527_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_fst_3514_);
v___x_3527_ = v___x_3473_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_fst_3514_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3527_);
v___x_3529_ = v___x_3520_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
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
else
{
lean_object* v_a_3533_; 
lean_dec(v_fst_3514_);
lean_del_object(v___x_3473_);
v_a_3533_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3517_, 1);
v_a_3319_ = v_a_3533_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3534_; 
lean_dec(v_fst_3514_);
lean_del_object(v___x_3473_);
lean_dec(v_a_3334_);
v_a_3534_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3515_, 1);
v_a_3319_ = v_a_3534_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3535_; 
lean_del_object(v___x_3473_);
lean_dec(v_a_3334_);
v_a_3535_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3512_, 1);
v_a_3319_ = v_a_3535_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3537_; 
lean_dec(v_a_3494_);
lean_del_object(v___x_3473_);
lean_dec(v_val_3471_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3432_);
v___x_3537_ = v___x_3496_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3432_);
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
else
{
lean_object* v_a_3540_; 
lean_del_object(v___x_3473_);
lean_dec(v_val_3471_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3540_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3493_, 1);
v_a_3319_ = v_a_3540_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3541_; 
lean_dec(v_a_3476_);
lean_del_object(v___x_3473_);
lean_dec(v_val_3471_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3541_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3477_, 1);
v_a_3319_ = v_a_3541_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3542_; 
lean_del_object(v___x_3473_);
lean_dec(v_val_3471_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3542_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3475_, 1);
v_a_3319_ = v_a_3542_;
goto v___jp_3318_;
}
}
}
else
{
lean_object* v___x_3545_; 
lean_dec(v_a_3467_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3432_);
v___x_3545_ = v___x_3469_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3432_);
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
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3548_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3466_, 1);
v_a_3319_ = v_a_3548_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3550_; 
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3457_);
v___x_3550_ = v___x_3366_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3457_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3550_);
v___x_3552_ = v___x_3463_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
else
{
lean_object* v_a_3556_; 
lean_dec_ref(v___x_3457_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3556_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3460_, 1);
v_a_3319_ = v_a_3556_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3557_; 
lean_dec_ref(v___x_3457_);
lean_dec_ref_known(v___x_3448_, 2);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3557_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3458_, 1);
v_a_3319_ = v_a_3557_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3558_; 
lean_dec(v_a_3442_);
lean_dec(v_a_3440_);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3558_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3443_, 1);
v_a_3319_ = v_a_3558_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3559_; 
lean_dec(v_a_3440_);
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3559_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3441_, 1);
v_a_3319_ = v_a_3559_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3560_; 
lean_dec(v_a_3438_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3560_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3439_, 1);
v_a_3319_ = v_a_3560_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3562_; 
lean_dec(v_a_3434_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3432_);
v___x_3562_ = v___x_3436_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3432_);
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
lean_object* v_a_3565_; 
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3565_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3433_, 1);
v_a_3319_ = v_a_3565_;
goto v___jp_3318_;
}
}
}
}
else
{
lean_object* v_a_3568_; 
lean_dec(v_a_3416_);
lean_dec(v_a_3406_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3568_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3417_, 1);
v_a_3319_ = v_a_3568_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3569_; 
lean_dec(v_a_3406_);
lean_dec(v_u_3404_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3569_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3415_, 1);
v_a_3319_ = v_a_3569_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3572_; 
lean_dec(v_a_3406_);
lean_dec(v_u_3404_);
lean_dec(v_u_3396_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3570_ = lean_box(0);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3570_);
v___x_3572_ = v___x_3412_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
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
lean_object* v_a_3575_; 
lean_dec(v_a_3406_);
lean_dec(v_u_3404_);
lean_dec(v_u_3396_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3575_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3409_, 1);
v_a_3319_ = v_a_3575_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3576_; 
lean_dec(v_a_3406_);
lean_dec(v_u_3404_);
lean_dec(v_u_3396_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3576_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3407_, 1);
v_a_3319_ = v_a_3576_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3577_; 
lean_dec(v_u_3404_);
lean_dec(v_u_3403_);
lean_dec(v_u_3396_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3577_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3405_, 1);
v_a_3319_ = v_a_3577_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3578_; 
lean_dec(v_u_3396_);
lean_dec(v_u_3395_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3578_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec_ref_known(v_a_3400_, 3);
v___y_3323_ = v___x_3578_;
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3579_; 
lean_dec(v_u_3396_);
lean_dec(v_u_3395_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3579_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec_ref_known(v_a_3400_, 3);
v___y_3323_ = v___x_3579_;
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3580_; 
lean_dec(v_u_3396_);
lean_dec(v_u_3395_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3580_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3400_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3400_);
v___y_3323_ = v___x_3580_;
goto v___jp_3322_;
}
}
else
{
lean_object* v_a_3581_; 
lean_dec(v_u_3396_);
lean_dec(v_u_3395_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3581_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3399_, 1);
v_a_3319_ = v_a_3581_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3582_; 
lean_dec(v_u_3396_);
lean_dec(v_u_3395_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3582_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3397_, 1);
v_a_3319_ = v_a_3582_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3583_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3583_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3392_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec_ref_known(v_a_3392_, 3);
v___y_3323_ = v___x_3583_;
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3584_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3584_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3392_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec_ref_known(v_a_3392_, 3);
v___y_3323_ = v___x_3584_;
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3585_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3585_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3392_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3392_);
v___y_3323_ = v___x_3585_;
goto v___jp_3322_;
}
}
else
{
lean_object* v_a_3586_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3586_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3391_, 1);
v_a_3319_ = v_a_3586_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3587_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3587_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3389_, 1);
v_a_3319_ = v_a_3587_;
goto v___jp_3318_;
}
}
}
else
{
lean_object* v___x_3588_; 
lean_del_object(v___x_3378_);
lean_del_object(v___x_3371_);
lean_del_object(v___x_3357_);
lean_dec(v_a_3341_);
lean_dec(v_a_3334_);
v___x_3588_ = l_Lean_Meta_isMonad_x3f(v_fst_3354_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3681_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3681_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3681_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
if (lean_obj_tag(v_a_3589_) == 1)
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_fst_3368_);
v___x_3595_ = v___x_3366_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_fst_3368_);
v___x_3595_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_snd_3369_);
v___x_3597_ = v___x_3352_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_snd_3369_);
v___x_3597_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3599_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 1);
lean_ctor_set(v___x_3343_, 0, v_snd_3355_);
v___x_3599_ = v___x_3343_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_snd_3355_);
v___x_3599_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___y_3602_; uint8_t v___y_3603_; lean_object* v_a_3625_; lean_object* v___x_3629_; 
v___x_3600_ = lean_box(0);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 1);
lean_ctor_set(v___x_3336_, 0, v_e_3305_);
v___x_3629_ = v___x_3336_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_e_3305_);
v___x_3629_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3628_;
}
v___jp_3601_:
{
if (v___y_3603_ == 0)
{
lean_object* v___x_3604_; 
lean_dec_ref(v___y_3602_);
lean_del_object(v___x_3591_);
v___x_3604_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3374_, v_a_3308_, v_a_3310_);
lean_dec(v_a_3374_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3612_);
v___x_3606_ = v___x_3604_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3600_);
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3600_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_a_3613_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3604_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3604_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v___x_3622_; 
lean_dec(v_a_3374_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set_tag(v___x_3591_, 1);
lean_ctor_set(v___x_3591_, 0, v___y_3602_);
v___x_3622_ = v___x_3591_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___y_3602_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
v___jp_3624_:
{
uint8_t v___x_3626_; 
v___x_3626_ = l_Lean_Exception_isInterrupt(v_a_3625_);
if (v___x_3626_ == 0)
{
uint8_t v___x_3627_; 
lean_inc_ref(v_a_3625_);
v___x_3627_ = l_Lean_Exception_isRuntime(v_a_3625_);
v___y_3602_ = v_a_3625_;
v___y_3603_ = v___x_3627_;
goto v___jp_3601_;
}
else
{
v___y_3602_ = v_a_3625_;
v___y_3603_ = v___x_3626_;
goto v___jp_3601_;
}
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3630_ = lean_unsigned_to_nat(6u);
v___x_3631_ = lean_mk_empty_array_with_capacity(v___x_3630_);
v___x_3632_ = lean_array_push(v___x_3631_, v___x_3595_);
v___x_3633_ = lean_array_push(v___x_3632_, v___x_3597_);
v___x_3634_ = lean_array_push(v___x_3633_, v___x_3599_);
v___x_3635_ = lean_array_push(v___x_3634_, v___x_3600_);
v___x_3636_ = lean_array_push(v___x_3635_, v_a_3589_);
v___x_3637_ = lean_array_push(v___x_3636_, v___x_3629_);
v___x_3638_ = l_Lean_Meta_mkAppOptM(v___x_3593_, v___x_3637_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3657_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3657_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3657_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Meta_expandCoe(v_a_3639_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3655_; 
lean_del_object(v___x_3591_);
lean_dec(v_a_3374_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_fst_3648_; lean_object* v___x_3650_; 
v_fst_3648_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_fst_3648_);
lean_dec(v_a_3644_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 1);
lean_ctor_set(v___x_3641_, 0, v_fst_3648_);
v___x_3650_ = v___x_3641_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_fst_3648_);
v___x_3650_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3650_);
v___x_3652_ = v___x_3646_;
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
lean_object* v_a_3656_; 
lean_del_object(v___x_3641_);
v_a_3656_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3643_, 1);
v_a_3625_ = v_a_3656_;
goto v___jp_3624_;
}
}
}
else
{
lean_object* v_a_3658_; 
v_a_3658_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3638_, 1);
v_a_3625_ = v_a_3658_;
goto v___jp_3624_;
}
}
}
}
}
}
else
{
lean_object* v___x_3663_; 
lean_del_object(v___x_3591_);
lean_dec(v_a_3589_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_del_object(v___x_3336_);
lean_dec_ref(v_e_3305_);
v___x_3663_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3374_, v_a_3308_, v_a_3310_);
lean_dec(v_a_3374_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3671_ == 0)
{
lean_object* v_unused_3672_; 
v_unused_3672_ = lean_ctor_get(v___x_3663_, 0);
lean_dec(v_unused_3672_);
v___x_3665_ = v___x_3663_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v___x_3663_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_box(0);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3663_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3663_);
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
}
}
else
{
lean_dec(v_a_3374_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_dec(v_snd_3355_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_del_object(v___x_3336_);
lean_dec_ref(v_e_3305_);
return v___x_3588_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_a_3374_);
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3683_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3375_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3375_);
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
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_del_object(v___x_3371_);
lean_dec(v_snd_3369_);
lean_dec(v_fst_3368_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3691_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3373_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3373_);
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
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
lean_dec(v_a_3360_);
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3701_ = lean_box(0);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3701_);
v___x_3703_ = v___x_3362_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_del_object(v___x_3357_);
lean_dec(v_snd_3355_);
lean_dec(v_fst_3354_);
lean_del_object(v___x_3352_);
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3706_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3359_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3359_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
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
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_a_3346_);
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v___x_3716_ = lean_box(0);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3716_);
v___x_3718_ = v___x_3348_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_del_object(v___x_3343_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3721_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3345_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3345_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
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
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_del_object(v___x_3336_);
lean_dec(v_a_3334_);
lean_dec_ref(v_e_3305_);
v_a_3730_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3338_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3338_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3739_, lean_object* v_expectedType_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3739_, v_expectedType_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3747_, lean_object* v_expectedType_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v___x_3754_; 
lean_inc_ref(v_expectedType_3748_);
lean_inc_ref(v_expr_3747_);
v___x_3754_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3747_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3834_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3834_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3834_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
if (lean_obj_tag(v_a_3755_) == 1)
{
lean_object* v_val_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_val_3759_ = lean_ctor_get(v_a_3755_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_a_3755_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3761_ = v_a_3755_;
v_isShared_3762_ = v_isSharedCheck_3771_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_val_3759_);
lean_dec(v_a_3755_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3771_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v_val_3759_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3764_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3766_);
v___x_3768_ = v___x_3757_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v___x_3772_; 
lean_del_object(v___x_3757_);
lean_dec(v_a_3755_);
lean_inc_ref(v_expectedType_3748_);
v___x_3772_ = l_Lean_Meta_whnfR(v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; uint8_t v___x_3774_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___x_3774_ = l_Lean_Expr_isForall(v_a_3773_);
lean_dec(v_a_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3747_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3775_;
}
else
{
lean_object* v___x_3776_; 
lean_inc_ref(v_expr_3747_);
v___x_3776_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3747_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
if (lean_obj_tag(v_a_3777_) == 1)
{
lean_object* v_val_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3816_; 
v_val_3778_ = lean_ctor_get(v_a_3777_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3780_ = v_a_3777_;
v_isShared_3781_ = v_isSharedCheck_3816_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_val_3778_);
lean_dec(v_a_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3816_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; 
lean_inc(v_a_3752_);
lean_inc_ref(v_a_3751_);
lean_inc(v_a_3750_);
lean_inc_ref(v_a_3749_);
lean_inc(v_val_3778_);
v___x_3782_ = lean_infer_type(v_val_3778_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
lean_inc_ref(v_expectedType_3748_);
v___x_3784_ = l_Lean_Meta_isExprDefEq(v_a_3783_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3799_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_unbox(v_a_3785_);
lean_dec(v_a_3785_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_del_object(v___x_3787_);
lean_del_object(v___x_3780_);
lean_dec(v_val_3778_);
v___x_3790_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3747_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v_val_3778_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3792_);
v___x_3794_ = v___x_3780_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3794_);
v___x_3796_ = v___x_3787_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_del_object(v___x_3780_);
lean_dec(v_val_3778_);
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_a_3800_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3784_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3784_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_del_object(v___x_3780_);
lean_dec(v_val_3778_);
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_a_3808_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3782_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3782_);
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
}
else
{
lean_object* v___x_3817_; 
lean_dec(v_a_3777_);
v___x_3817_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3747_, v_expectedType_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3817_;
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_a_3818_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3776_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3776_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_a_3826_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3772_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3772_);
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
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_expectedType_3748_);
lean_dec_ref(v_expr_3747_);
v_a_3835_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3754_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3754_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3843_, lean_object* v_expectedType_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3843_, v_expectedType_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3851_, lean_object* v_expectedType_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3851_, v_expectedType_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3883_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3883_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3883_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
switch(lean_obj_tag(v_a_3859_))
{
case 0:
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3863_ = lean_box(0);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3863_);
v___x_3865_ = v___x_3861_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
case 1:
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3878_; 
v_a_3867_ = lean_ctor_get(v_a_3859_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3859_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3869_ = v_a_3859_;
v_isShared_3870_ = v_isSharedCheck_3878_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v_a_3859_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3878_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_fst_3871_; lean_object* v___x_3873_; 
v_fst_3871_ = lean_ctor_get(v_a_3867_, 0);
lean_inc(v_fst_3871_);
lean_dec(v_a_3867_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v_fst_3871_);
v___x_3873_ = v___x_3869_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_fst_3871_);
v___x_3873_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3875_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3873_);
v___x_3875_ = v___x_3861_;
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
default: 
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3879_ = lean_box(2);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3879_);
v___x_3881_ = v___x_3861_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3858_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3858_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3892_, lean_object* v_expectedType_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Meta_coerce_x3f(v_expr_3892_, v_expectedType_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
return v_res_3899_;
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
