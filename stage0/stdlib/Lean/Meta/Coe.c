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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0;
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
static lean_once_cell_t l_Lean_Meta_expandCoe___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_expandCoe___closed__2;
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
static lean_once_cell_t l_Lean_Meta_isTypeApp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_isTypeApp_x3f___closed__0;
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
v___x_244_ = lean_st_ref_set(v___y_205_, v___x_243_);
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
size_t v_x_37515__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_37515__boxed_301_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_res_302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_298_, v_x_37515__boxed_301_, v_x_300_);
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
lean_object* v___x_361_; lean_object* v_env_362_; uint8_t v_isExporting_363_; lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v___x_366_; lean_object* v_entry_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___x_415_; uint8_t v___x_416_; uint8_t v___x_417_; 
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
v___x_417_ = lean_bool_not(v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref_known(v_entry_367_, 1);
lean_dec(v_hint_354_);
lean_dec(v_mod_352_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___y_355_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v_options_421_; uint8_t v_hasTrace_422_; 
v_options_421_ = lean_ctor_get(v___y_358_, 2);
v_hasTrace_422_ = lean_ctor_get_uint8(v_options_421_, sizeof(void*)*1);
if (v_hasTrace_422_ == 0)
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
lean_object* v_inheritedTraceOptions_423_; lean_object* v_cls_424_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_inheritedTraceOptions_423_ = lean_ctor_get(v___y_358_, 13);
v_cls_424_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_446_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_423_, v_options_421_, v___x_446_);
if (v___x_447_ == 0)
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
lean_object* v___x_448_; lean_object* v___y_450_; 
v___x_448_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_363_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_450_ = v___x_458_;
goto v___jp_449_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v___y_450_);
v___x_451_ = l_Lean_stringToMessageData(v___y_450_);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_448_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
if (v_isMeta_353_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_433_ = v___x_454_;
v___y_434_ = v___x_455_;
goto v___jp_432_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_433_ = v___x_454_;
v___y_434_ = v___x_456_;
goto v___jp_432_;
}
}
}
v___jp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___y_426_);
lean_ctor_set(v___x_428_, 1, v___y_427_);
v___x_429_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_424_, v___x_428_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_snd_431_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_snd_431_ = lean_ctor_get(v_a_430_, 1);
lean_inc(v_snd_431_);
lean_dec(v_a_430_);
v___y_372_ = v_snd_431_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_359_;
goto v___jp_371_;
}
else
{
lean_dec_ref_known(v_entry_367_, 1);
return v___x_429_;
}
}
v___jp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
lean_inc_ref(v___y_434_);
v___x_435_ = l_Lean_stringToMessageData(v___y_434_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___y_433_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_MessageData_ofName(v_mod_352_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_Name_isAnonymous(v_hint_354_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_443_ = l_Lean_MessageData_ofName(v_hint_354_);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___y_426_ = v___x_440_;
v___y_427_ = v___x_444_;
goto v___jp_425_;
}
else
{
lean_object* v___x_445_; 
lean_dec(v_hint_354_);
v___x_445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_426_ = v___x_440_;
v___y_427_ = v___x_445_;
goto v___jp_425_;
}
}
}
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
v___x_393_ = lean_st_ref_set(v___y_374_, v___x_392_);
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
v___x_405_ = lean_st_ref_set(v___y_373_, v___x_404_);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_459_, lean_object* v_isMeta_460_, lean_object* v_hint_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v_isMeta_boxed_468_; lean_object* v_res_469_; 
v_isMeta_boxed_468_ = lean_unbox(v_isMeta_460_);
v_res_469_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_459_, v_isMeta_boxed_468_, v_hint_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_box(0);
return v___x_472_;
}
else
{
lean_object* v_key_473_; lean_object* v_value_474_; lean_object* v_tail_475_; uint8_t v___x_476_; 
v_key_473_ = lean_ctor_get(v_x_471_, 0);
v_value_474_ = lean_ctor_get(v_x_471_, 1);
v_tail_475_ = lean_ctor_get(v_x_471_, 2);
v___x_476_ = lean_name_eq(v_key_473_, v_a_470_);
if (v___x_476_ == 0)
{
v_x_471_ = v_tail_475_;
goto _start;
}
else
{
lean_object* v___x_478_; 
lean_inc(v_value_474_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_value_474_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_479_, v_x_480_);
lean_dec(v_x_480_);
lean_dec(v_a_479_);
return v_res_481_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_482_; uint64_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1723u);
v___x_483_ = lean_uint64_of_nat(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_buckets_486_; lean_object* v___x_487_; uint64_t v___y_489_; 
v_buckets_486_ = lean_ctor_get(v_m_484_, 1);
v___x_487_ = lean_array_get_size(v_buckets_486_);
if (lean_obj_tag(v_a_485_) == 0)
{
uint64_t v___x_503_; 
v___x_503_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
v___y_489_ = v___x_503_;
goto v___jp_488_;
}
else
{
uint64_t v_hash_504_; 
v_hash_504_ = lean_ctor_get_uint64(v_a_485_, sizeof(void*)*2);
v___y_489_ = v_hash_504_;
goto v___jp_488_;
}
v___jp_488_:
{
uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v_fold_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_490_ = 32ULL;
v___x_491_ = lean_uint64_shift_right(v___y_489_, v___x_490_);
v_fold_492_ = lean_uint64_xor(v___y_489_, v___x_491_);
v___x_493_ = 16ULL;
v___x_494_ = lean_uint64_shift_right(v_fold_492_, v___x_493_);
v___x_495_ = lean_uint64_xor(v_fold_492_, v___x_494_);
v___x_496_ = lean_uint64_to_usize(v___x_495_);
v___x_497_ = lean_usize_of_nat(v___x_487_);
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_sub(v___x_497_, v___x_498_);
v___x_500_ = lean_usize_land(v___x_496_, v___x_499_);
v___x_501_ = lean_array_uget_borrowed(v_buckets_486_, v___x_500_);
v___x_502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_485_, v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_m_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_508_, lean_object* v_declName_509_, lean_object* v_as_510_, size_t v_sz_511_, size_t v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_lt(v_i_512_, v_sz_511_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_declName_509_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_b_513_);
lean_ctor_set(v___x_521_, 1, v___y_514_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v_modules_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v_toImport_528_; lean_object* v_module_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v___x_523_ = l_Lean_Environment_header(v___x_508_);
v_modules_524_ = lean_ctor_get(v___x_523_, 3);
lean_inc_ref(v_modules_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_526_ = lean_array_uget_borrowed(v_as_510_, v_i_512_);
v___x_527_ = lean_array_get(v___x_525_, v_modules_524_, v_a_526_);
lean_dec_ref(v_modules_524_);
v_toImport_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_toImport_528_);
lean_dec(v___x_527_);
v_module_529_ = lean_ctor_get(v_toImport_528_, 0);
lean_inc(v_module_529_);
lean_dec_ref(v_toImport_528_);
v___x_530_ = 0;
lean_inc(v_declName_509_);
v___x_531_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_529_, v___x_530_, v_declName_509_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_snd_533_; lean_object* v___x_534_; size_t v___x_535_; size_t v___x_536_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v_snd_533_ = lean_ctor_get(v_a_532_, 1);
lean_inc(v_snd_533_);
lean_dec(v_a_532_);
v___x_534_ = lean_box(0);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_512_, v___x_535_);
v_i_512_ = v___x_536_;
v_b_513_ = v___x_534_;
v___y_514_ = v_snd_533_;
goto _start;
}
else
{
lean_dec(v_declName_509_);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_538_, lean_object* v_declName_539_, lean_object* v_as_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_551_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_538_, v_declName_539_, v_as_540_, v_sz_boxed_550_, v_i_boxed_551_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec_ref(v_as_540_);
lean_dec_ref(v___x_538_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_556_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_557_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_556_, v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_560_, uint8_t v_isMeta_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v_env_573_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___x_598_; 
v___x_568_ = lean_st_ref_get(v___y_566_);
v_env_573_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_env_573_);
lean_dec(v___x_568_);
v___x_598_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_573_, v_declName_560_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_dec_ref(v_env_573_);
lean_dec(v_declName_560_);
goto v___jp_569_;
}
else
{
lean_object* v_val_599_; lean_object* v___x_600_; lean_object* v_modules_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = l_Lean_Environment_header(v_env_573_);
v_modules_601_ = lean_ctor_get(v___x_600_, 3);
lean_inc_ref(v_modules_601_);
lean_dec_ref(v___x_600_);
v___x_602_ = lean_array_get_size(v_modules_601_);
v___x_603_ = lean_nat_dec_lt(v_val_599_, v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v_modules_601_);
lean_dec(v_val_599_);
lean_dec_ref(v_env_573_);
lean_dec(v_declName_560_);
goto v___jp_569_;
}
else
{
lean_object* v___x_604_; lean_object* v_env_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___y_609_; 
v___x_604_ = lean_st_ref_get(v___y_566_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_607_ = lean_array_fget(v_modules_601_, v_val_599_);
lean_dec(v_val_599_);
lean_dec_ref(v_modules_601_);
if (v_isMeta_561_ == 0)
{
lean_dec_ref(v_env_605_);
v___y_609_ = v_isMeta_561_;
goto v___jp_608_;
}
else
{
uint8_t v___x_622_; uint8_t v___x_623_; 
lean_inc(v_declName_560_);
v___x_622_ = l_Lean_isMarkedMeta(v_env_605_, v_declName_560_);
v___x_623_ = lean_bool_not(v___x_622_);
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v_toImport_610_; lean_object* v_module_611_; lean_object* v___x_612_; 
v_toImport_610_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_toImport_610_);
lean_dec(v___x_607_);
v_module_611_ = lean_ctor_get(v_toImport_610_, 0);
lean_inc(v_module_611_);
lean_dec_ref(v_toImport_610_);
lean_inc(v_declName_560_);
v___x_612_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_611_, v___y_609_, v_declName_560_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v_snd_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v_snd_614_ = lean_ctor_get(v_a_613_, 1);
lean_inc(v_snd_614_);
lean_dec(v_a_613_);
v___x_615_ = l_Lean_indirectModUseExt;
v___x_616_ = lean_box(1);
v___x_617_ = lean_box(0);
lean_inc_ref(v_env_573_);
v___x_618_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_606_, v___x_615_, v_env_573_, v___x_616_, v___x_617_);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_618_, v_declName_560_);
lean_dec(v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_575_ = v_snd_614_;
v___y_576_ = v___x_620_;
goto v___jp_574_;
}
else
{
lean_object* v_val_621_; 
v_val_621_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v___x_619_, 1);
v___y_575_ = v_snd_614_;
v___y_576_ = v_val_621_;
goto v___jp_574_;
}
}
else
{
lean_dec_ref(v_env_573_);
lean_dec(v_declName_560_);
return v___x_612_;
}
}
}
}
v___jp_569_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___y_562_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
v___jp_574_:
{
lean_object* v___x_577_; size_t v_sz_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_box(0);
v_sz_578_ = lean_array_size(v___y_576_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_573_, v_declName_560_, v___y_576_, v_sz_578_, v___x_579_, v___x_577_, v___y_575_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_env_573_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_597_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_597_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_597_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_597_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_595_; 
v_snd_585_ = lean_ctor_get(v_a_581_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_a_581_, 0);
lean_dec(v_unused_596_);
v___x_587_ = v_a_581_;
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_dec(v_a_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_577_);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_585_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_590_);
v___x_592_ = v___x_583_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_624_, lean_object* v_isMeta_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v_isMeta_boxed_632_; lean_object* v_res_633_; 
v_isMeta_boxed_632_ = lean_unbox(v_isMeta_625_);
v_res_633_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_624_, v_isMeta_boxed_632_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___y_649_; lean_object* v_f_653_; uint8_t v___x_654_; 
v_f_653_ = l_Lean_Expr_getAppFn(v_e_641_);
v___x_654_ = l_Lean_Expr_isConst(v_f_653_);
if (v___x_654_ == 0)
{
lean_dec_ref(v_f_653_);
lean_dec_ref(v_e_641_);
v___y_649_ = v___y_642_;
goto v___jp_648_;
}
else
{
lean_object* v___x_655_; lean_object* v_env_656_; lean_object* v_declName_657_; uint8_t v___x_658_; 
v___x_655_ = lean_st_ref_get(v___y_646_);
v_env_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc_ref(v_env_656_);
lean_dec(v___x_655_);
v_declName_657_ = l_Lean_Expr_constName_x21(v_f_653_);
lean_dec_ref(v_f_653_);
lean_inc(v_declName_657_);
v___x_658_ = l_Lean_Meta_isCoeDecl(v_env_656_, v_declName_657_);
if (v___x_658_ == 0)
{
lean_dec(v_declName_657_);
lean_dec_ref(v_e_641_);
v___y_649_ = v___y_642_;
goto v___jp_648_;
}
else
{
lean_object* v___x_659_; 
lean_inc(v_declName_657_);
lean_inc_ref(v_e_641_);
v___x_659_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_641_, v_declName_657_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; uint8_t v___x_661_; lean_object* v___x_662_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = 0;
v___x_662_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_660_, v___x_661_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v_snd_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_715_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v_snd_664_ = lean_ctor_get(v_a_663_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_a_663_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_a_663_, 0);
lean_dec(v_unused_716_);
v___x_666_ = v_a_663_;
v_isShared_667_ = v_isSharedCheck_715_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_snd_664_);
lean_dec(v_a_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_715_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; 
lean_inc_ref(v_e_641_);
v___x_668_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_641_, v___x_661_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_706_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_706_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_706_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_706_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
if (lean_obj_tag(v_a_669_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_705_; 
v_val_673_ = lean_ctor_get(v_a_669_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_705_ == 0)
{
v___x_675_ = v_a_669_;
v_isShared_676_ = v_isSharedCheck_705_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v_a_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_705_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___y_678_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_690_ = lean_name_eq(v_declName_657_, v___x_689_);
lean_dec(v_declName_657_);
if (v___x_690_ == 0)
{
lean_dec_ref(v_e_641_);
v___y_678_ = v_snd_664_;
goto v___jp_677_;
}
else
{
lean_object* v_dummy_691_; lean_object* v_nargs_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_dummy_691_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_692_ = l_Lean_Expr_getAppNumArgs(v_e_641_);
lean_inc(v_nargs_692_);
v___x_693_ = lean_mk_array(v_nargs_692_, v_dummy_691_);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_sub(v_nargs_692_, v___x_694_);
lean_dec(v_nargs_692_);
v___x_696_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_641_, v___x_693_, v___x_695_);
v___x_697_ = lean_unsigned_to_nat(2u);
v___x_698_ = lean_array_get_size(v___x_696_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec_ref(v___x_696_);
v___y_678_ = v_snd_664_;
goto v___jp_677_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_array_fget(v___x_696_, v___x_697_);
lean_dec_ref(v___x_696_);
v___x_701_ = l_Lean_Expr_getAppFn(v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = l_Lean_Expr_isConst(v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v___x_701_);
v___y_678_ = v_snd_664_;
goto v___jp_677_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = l_Lean_Expr_constName_x21(v___x_701_);
lean_dec_ref(v___x_701_);
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_snd_664_);
v___y_678_ = v___x_704_;
goto v___jp_677_;
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = l_Lean_Expr_headBeta(v_val_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_679_);
v___x_681_ = v___x_675_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_688_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___y_678_);
lean_ctor_set(v___x_666_, 0, v___x_681_);
v___x_683_ = v___x_666_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___y_678_);
v___x_683_ = v_reuseFailAlloc_687_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_683_);
v___x_685_ = v___x_671_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_671_);
lean_dec(v_a_669_);
lean_del_object(v___x_666_);
lean_dec(v_declName_657_);
lean_dec_ref(v_e_641_);
v___y_649_ = v_snd_664_;
goto v___jp_648_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_666_);
lean_dec(v_snd_664_);
lean_dec(v_declName_657_);
lean_dec_ref(v_e_641_);
v_a_707_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_668_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_668_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_declName_657_);
lean_dec_ref(v_e_641_);
v_a_717_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_662_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_662_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_declName_657_);
lean_dec(v___y_642_);
lean_dec_ref(v_e_641_);
v_a_725_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_659_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_659_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_649_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_expandCoe___lam__1(v_e_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_742_);
v___x_750_ = lean_apply_8(v_k_741_, v_b_744_, v___y_742_, v___y_743_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, lean_box(0));
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v_b_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_751_, v___y_752_, v___y_753_, v_b_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_752_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_761_, uint8_t v_bi_762_, lean_object* v_type_763_, lean_object* v_k_764_, uint8_t v_kind_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; 
lean_inc(v___y_766_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_773_, 0, v_k_764_);
lean_closure_set(v___f_773_, 1, v___y_766_);
lean_closure_set(v___f_773_, 2, v___y_767_);
v___x_774_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_761_, v_bi_762_, v_type_763_, v___f_773_, v_kind_765_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_791_, lean_object* v_bi_792_, lean_object* v_type_793_, lean_object* v_k_794_, lean_object* v_kind_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v_bi_boxed_803_; uint8_t v_kind_boxed_804_; lean_object* v_res_805_; 
v_bi_boxed_803_ = lean_unbox(v_bi_792_);
v_kind_boxed_804_ = lean_unbox(v_kind_795_);
v_res_805_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_791_, v_bi_boxed_803_, v_type_793_, v_k_794_, v_kind_boxed_804_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_796_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_806_);
lean_ctor_set(v___x_813_, 1, v___y_807_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_823_, lean_object* v_type_824_, lean_object* v_val_825_, lean_object* v_k_826_, uint8_t v_nondep_827_, uint8_t v_kind_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; 
lean_inc(v___y_829_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_836_, 0, v_k_826_);
lean_closure_set(v___f_836_, 1, v___y_829_);
lean_closure_set(v___f_836_, 2, v___y_830_);
v___x_837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_823_, v_type_824_, v_val_825_, v___f_836_, v_nondep_827_, v_kind_828_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_837_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_837_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_854_, lean_object* v_type_855_, lean_object* v_val_856_, lean_object* v_k_857_, lean_object* v_nondep_858_, lean_object* v_kind_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v_nondep_boxed_867_; uint8_t v_kind_boxed_868_; lean_object* v_res_869_; 
v_nondep_boxed_867_ = lean_unbox(v_nondep_858_);
v_kind_boxed_868_ = lean_unbox(v_kind_859_);
v_res_869_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_854_, v_type_855_, v_val_856_, v_k_857_, v_nondep_boxed_867_, v_kind_boxed_868_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_860_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_dec(v_b_871_);
lean_dec_ref(v_a_870_);
return v_x_872_;
}
else
{
lean_object* v_key_873_; lean_object* v_value_874_; lean_object* v_tail_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_887_; 
v_key_873_ = lean_ctor_get(v_x_872_, 0);
v_value_874_ = lean_ctor_get(v_x_872_, 1);
v_tail_875_ = lean_ctor_get(v_x_872_, 2);
v_isSharedCheck_887_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_887_ == 0)
{
v___x_877_ = v_x_872_;
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_tail_875_);
lean_inc(v_value_874_);
lean_inc(v_key_873_);
lean_dec(v_x_872_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_887_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_ExprStructEq_beq(v_key_873_, v_a_870_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_870_, v_b_871_, v_tail_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 2, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_key_873_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_value_874_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v_value_874_);
lean_dec(v_key_873_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v_b_871_);
lean_ctor_set(v___x_877_, 0, v_a_870_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_b_871_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_tail_875_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
if (lean_obj_tag(v_x_889_) == 0)
{
uint8_t v___x_890_; 
v___x_890_ = 0;
return v___x_890_;
}
else
{
lean_object* v_key_891_; lean_object* v_tail_892_; uint8_t v___x_893_; 
v_key_891_ = lean_ctor_get(v_x_889_, 0);
v_tail_892_ = lean_ctor_get(v_x_889_, 2);
v___x_893_ = l_Lean_ExprStructEq_beq(v_key_891_, v_a_888_);
if (v___x_893_ == 0)
{
v_x_889_ = v_tail_892_;
goto _start;
}
else
{
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_895_, v_x_896_);
lean_dec(v_x_896_);
lean_dec_ref(v_a_895_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
return v_x_899_;
}
else
{
lean_object* v_key_901_; lean_object* v_value_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_926_; 
v_key_901_ = lean_ctor_get(v_x_900_, 0);
v_value_902_ = lean_ctor_get(v_x_900_, 1);
v_tail_903_ = lean_ctor_get(v_x_900_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_x_900_);
if (v_isSharedCheck_926_ == 0)
{
v___x_905_ = v_x_900_;
v_isShared_906_ = v_isSharedCheck_926_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_inc(v_value_902_);
lean_inc(v_key_901_);
lean_dec(v_x_900_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_926_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v_fold_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_907_ = lean_array_get_size(v_x_899_);
v___x_908_ = l_Lean_ExprStructEq_hash(v_key_901_);
v___x_909_ = 32ULL;
v___x_910_ = lean_uint64_shift_right(v___x_908_, v___x_909_);
v_fold_911_ = lean_uint64_xor(v___x_908_, v___x_910_);
v___x_912_ = 16ULL;
v___x_913_ = lean_uint64_shift_right(v_fold_911_, v___x_912_);
v___x_914_ = lean_uint64_xor(v_fold_911_, v___x_913_);
v___x_915_ = lean_uint64_to_usize(v___x_914_);
v___x_916_ = lean_usize_of_nat(v___x_907_);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_sub(v___x_916_, v___x_917_);
v___x_919_ = lean_usize_land(v___x_915_, v___x_918_);
v___x_920_ = lean_array_uget_borrowed(v_x_899_, v___x_919_);
lean_inc(v___x_920_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 2, v___x_920_);
v___x_922_ = v___x_905_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_key_901_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_value_902_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___x_920_);
v___x_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_array_uset(v_x_899_, v___x_919_, v___x_922_);
v_x_899_ = v___x_923_;
v_x_900_ = v_tail_903_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_927_, lean_object* v_source_928_, lean_object* v_target_929_){
_start:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_array_get_size(v_source_928_);
v___x_931_ = lean_nat_dec_lt(v_i_927_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v_source_928_);
lean_dec(v_i_927_);
return v_target_929_;
}
else
{
lean_object* v_es_932_; lean_object* v___x_933_; lean_object* v_source_934_; lean_object* v_target_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_es_932_ = lean_array_fget(v_source_928_, v_i_927_);
v___x_933_ = lean_box(0);
v_source_934_ = lean_array_fset(v_source_928_, v_i_927_, v___x_933_);
v_target_935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_929_, v_es_932_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_i_927_, v___x_936_);
lean_dec(v_i_927_);
v_i_927_ = v___x_937_;
v_source_928_ = v_source_934_;
v_target_929_ = v_target_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_nbuckets_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_940_ = lean_array_get_size(v_data_939_);
v___x_941_ = lean_unsigned_to_nat(2u);
v_nbuckets_942_ = lean_nat_mul(v___x_940_, v___x_941_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_box(0);
v___x_945_ = lean_mk_array(v_nbuckets_942_, v___x_944_);
v___x_946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_943_, v_data_939_, v___x_945_);
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
v___x_1001_ = lean_st_ref_set(v_a_995_, v___x_1000_);
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
lean_object* v___y_1037_; lean_object* v_fileName_1054_; lean_object* v_fileMap_1055_; lean_object* v_options_1056_; lean_object* v_currRecDepth_1057_; lean_object* v_maxRecDepth_1058_; lean_object* v_ref_1059_; lean_object* v_currNamespace_1060_; lean_object* v_openDecls_1061_; lean_object* v_initHeartbeats_1062_; lean_object* v_maxHeartbeats_1063_; lean_object* v_quotContext_1064_; lean_object* v_currMacroScope_1065_; uint8_t v_diag_1066_; lean_object* v_cancelTk_x3f_1067_; uint8_t v_suppressElabErrors_1068_; lean_object* v_inheritedTraceOptions_1069_; uint8_t v___y_1071_; lean_object* v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; 
v_fileName_1054_ = lean_ctor_get(v___y_1033_, 0);
v_fileMap_1055_ = lean_ctor_get(v___y_1033_, 1);
v_options_1056_ = lean_ctor_get(v___y_1033_, 2);
v_currRecDepth_1057_ = lean_ctor_get(v___y_1033_, 3);
v_maxRecDepth_1058_ = lean_ctor_get(v___y_1033_, 4);
v_ref_1059_ = lean_ctor_get(v___y_1033_, 5);
v_currNamespace_1060_ = lean_ctor_get(v___y_1033_, 6);
v_openDecls_1061_ = lean_ctor_get(v___y_1033_, 7);
v_initHeartbeats_1062_ = lean_ctor_get(v___y_1033_, 8);
v_maxHeartbeats_1063_ = lean_ctor_get(v___y_1033_, 9);
v_quotContext_1064_ = lean_ctor_get(v___y_1033_, 10);
v_currMacroScope_1065_ = lean_ctor_get(v___y_1033_, 11);
v_diag_1066_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*14);
v_cancelTk_x3f_1067_ = lean_ctor_get(v___y_1033_, 12);
v_suppressElabErrors_1068_ = lean_ctor_get_uint8(v___y_1033_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1069_ = lean_ctor_get(v___y_1033_, 13);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_nat_dec_eq(v_maxRecDepth_1058_, v___x_1077_);
v___x_1079_ = lean_bool_not(v___x_1078_);
if (v___x_1079_ == 0)
{
v___y_1071_ = v___x_1079_;
goto v___jp_1070_;
}
else
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_nat_dec_eq(v_currRecDepth_1057_, v_maxRecDepth_1058_);
v___y_1071_ = v___x_1080_;
goto v___jp_1070_;
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
v___jp_1070_:
{
if (v___y_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_currRecDepth_1057_, v___x_1072_);
lean_inc_ref(v_inheritedTraceOptions_1069_);
lean_inc(v_cancelTk_x3f_1067_);
lean_inc(v_currMacroScope_1065_);
lean_inc(v_quotContext_1064_);
lean_inc(v_maxHeartbeats_1063_);
lean_inc(v_initHeartbeats_1062_);
lean_inc(v_openDecls_1061_);
lean_inc(v_currNamespace_1060_);
lean_inc(v_ref_1059_);
lean_inc(v_maxRecDepth_1058_);
lean_inc_ref(v_options_1056_);
lean_inc_ref(v_fileMap_1055_);
lean_inc_ref(v_fileName_1054_);
v___x_1074_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1074_, 0, v_fileName_1054_);
lean_ctor_set(v___x_1074_, 1, v_fileMap_1055_);
lean_ctor_set(v___x_1074_, 2, v_options_1056_);
lean_ctor_set(v___x_1074_, 3, v___x_1073_);
lean_ctor_set(v___x_1074_, 4, v_maxRecDepth_1058_);
lean_ctor_set(v___x_1074_, 5, v_ref_1059_);
lean_ctor_set(v___x_1074_, 6, v_currNamespace_1060_);
lean_ctor_set(v___x_1074_, 7, v_openDecls_1061_);
lean_ctor_set(v___x_1074_, 8, v_initHeartbeats_1062_);
lean_ctor_set(v___x_1074_, 9, v_maxHeartbeats_1063_);
lean_ctor_set(v___x_1074_, 10, v_quotContext_1064_);
lean_ctor_set(v___x_1074_, 11, v_currMacroScope_1065_);
lean_ctor_set(v___x_1074_, 12, v_cancelTk_x3f_1067_);
lean_ctor_set(v___x_1074_, 13, v_inheritedTraceOptions_1069_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*14, v_diag_1066_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*14 + 1, v_suppressElabErrors_1068_);
lean_inc(v___y_1034_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1029_);
v___x_1075_ = lean_apply_7(v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___x_1074_, v___y_1034_, lean_box(0));
v___y_1037_ = v___x_1075_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v___y_1030_);
lean_dec_ref(v_x_1028_);
lean_inc(v_ref_1059_);
v___x_1076_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1059_);
v___y_1037_ = v___x_1076_;
goto v___jp_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_box(0);
return v___x_1092_;
}
else
{
lean_object* v_key_1093_; lean_object* v_value_1094_; lean_object* v_tail_1095_; uint8_t v___x_1096_; 
v_key_1093_ = lean_ctor_get(v_x_1091_, 0);
v_value_1094_ = lean_ctor_get(v_x_1091_, 1);
v_tail_1095_ = lean_ctor_get(v_x_1091_, 2);
v___x_1096_ = l_Lean_ExprStructEq_beq(v_key_1093_, v_a_1090_);
if (v___x_1096_ == 0)
{
v_x_1091_ = v_tail_1095_;
goto _start;
}
else
{
lean_object* v___x_1098_; 
lean_inc(v_value_1094_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_value_1094_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1099_, v_x_1100_);
lean_dec(v_x_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_buckets_1104_; lean_object* v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v_fold_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_buckets_1104_ = lean_ctor_get(v_m_1102_, 1);
v___x_1105_ = lean_array_get_size(v_buckets_1104_);
v___x_1106_ = l_Lean_ExprStructEq_hash(v_a_1103_);
v___x_1107_ = 32ULL;
v___x_1108_ = lean_uint64_shift_right(v___x_1106_, v___x_1107_);
v_fold_1109_ = lean_uint64_xor(v___x_1106_, v___x_1108_);
v___x_1110_ = 16ULL;
v___x_1111_ = lean_uint64_shift_right(v_fold_1109_, v___x_1110_);
v___x_1112_ = lean_uint64_xor(v_fold_1109_, v___x_1111_);
v___x_1113_ = lean_uint64_to_usize(v___x_1112_);
v___x_1114_ = lean_usize_of_nat(v___x_1105_);
v___x_1115_ = ((size_t)1ULL);
v___x_1116_ = lean_usize_sub(v___x_1114_, v___x_1115_);
v___x_1117_ = lean_usize_land(v___x_1113_, v___x_1116_);
v___x_1118_ = lean_array_uget_borrowed(v_buckets_1104_, v___x_1117_);
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1103_, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1120_, v_a_1121_);
lean_dec_ref(v_a_1121_);
lean_dec_ref(v_m_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1123_, lean_object* v_x_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_apply_1(v_x_1124_, lean_box(0));
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___y_1125_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1134_, v_x_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1146_, lean_object* v_pre_1147_, lean_object* v_post_1148_, uint8_t v_usedLetOnly_1149_, uint8_t v_skipConstInApp_1150_, uint8_t v_skipInstances_1151_, lean_object* v_body_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_array_push(v_fvars_1146_, v_x_1153_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1147_, v_post_1148_, v_usedLetOnly_1149_, v_skipConstInApp_1150_, v_skipInstances_1151_, v___x_1161_, v_body_1152_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1163_, lean_object* v_pre_1164_, lean_object* v_post_1165_, lean_object* v_usedLetOnly_1166_, lean_object* v_skipConstInApp_1167_, lean_object* v_skipInstances_1168_, lean_object* v_body_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_usedLetOnly_boxed_1178_; uint8_t v_skipConstInApp_boxed_1179_; uint8_t v_skipInstances_boxed_1180_; lean_object* v_res_1181_; 
v_usedLetOnly_boxed_1178_ = lean_unbox(v_usedLetOnly_1166_);
v_skipConstInApp_boxed_1179_ = lean_unbox(v_skipConstInApp_1167_);
v_skipInstances_boxed_1180_ = lean_unbox(v_skipInstances_1168_);
v_res_1181_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1163_, v_pre_1164_, v_post_1165_, v_usedLetOnly_boxed_1178_, v_skipConstInApp_boxed_1179_, v_skipInstances_boxed_1180_, v_body_1169_, v_x_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1171_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1182_, lean_object* v_post_1183_, uint8_t v_usedLetOnly_1184_, uint8_t v_skipConstInApp_1185_, uint8_t v_skipInstances_1186_, lean_object* v_e_1187_, lean_object* v_a_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
lean_inc_ref(v_post_1183_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
lean_inc(v___y_1191_);
lean_inc_ref(v___y_1190_);
lean_inc_ref(v_e_1187_);
v___x_1195_ = lean_apply_7(v_post_1183_, v_e_1187_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, lean_box(0));
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1227_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1227_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1227_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1226_; 
v_fst_1200_ = lean_ctor_get(v_a_1196_, 0);
v_snd_1201_ = lean_ctor_get(v_a_1196_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_a_1196_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1203_ = v_a_1196_;
v_isShared_1204_ = v_isSharedCheck_1226_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
lean_dec(v_a_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1226_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___y_1206_; 
switch(lean_obj_tag(v_fst_1200_))
{
case 0:
{
lean_object* v_e_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1203_);
lean_del_object(v___x_1198_);
lean_dec_ref(v_e_1187_);
lean_dec_ref(v_post_1183_);
lean_dec_ref(v_pre_1182_);
v_e_1213_ = lean_ctor_get(v_fst_1200_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_fst_1200_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v_fst_1200_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_e_1213_);
lean_dec(v_fst_1200_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_e_1213_);
lean_ctor_set(v___x_1217_, 1, v_snd_1201_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
case 1:
{
lean_object* v_e_1222_; lean_object* v___x_1223_; 
lean_del_object(v___x_1203_);
lean_del_object(v___x_1198_);
lean_dec_ref(v_e_1187_);
v_e_1222_ = lean_ctor_get(v_fst_1200_, 0);
lean_inc_ref(v_e_1222_);
lean_dec_ref_known(v_fst_1200_, 1);
v___x_1223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1182_, v_post_1183_, v_usedLetOnly_1184_, v_skipConstInApp_1185_, v_skipInstances_1186_, v_e_1222_, v_a_1188_, v_snd_1201_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1223_;
}
default: 
{
lean_object* v_e_x3f_1224_; 
lean_dec_ref(v_post_1183_);
lean_dec_ref(v_pre_1182_);
v_e_x3f_1224_ = lean_ctor_get(v_fst_1200_, 0);
lean_inc(v_e_x3f_1224_);
lean_dec_ref_known(v_fst_1200_, 1);
if (lean_obj_tag(v_e_x3f_1224_) == 0)
{
v___y_1206_ = v_e_1187_;
goto v___jp_1205_;
}
else
{
lean_object* v_val_1225_; 
lean_dec_ref(v_e_1187_);
v_val_1225_ = lean_ctor_get(v_e_x3f_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v_e_x3f_1224_, 1);
v___y_1206_ = v_val_1225_;
goto v___jp_1205_;
}
}
}
v___jp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___y_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___y_1206_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_snd_1201_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1208_);
v___x_1210_ = v___x_1198_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_e_1187_);
lean_dec_ref(v_post_1183_);
lean_dec_ref(v_pre_1182_);
v_a_1228_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1195_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1195_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1236_, lean_object* v_post_1237_, uint8_t v_usedLetOnly_1238_, uint8_t v_skipConstInApp_1239_, uint8_t v_skipInstances_1240_, lean_object* v_fvars_1241_, lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
if (lean_obj_tag(v_e_1242_) == 6)
{
lean_object* v_binderName_1250_; lean_object* v_binderType_1251_; lean_object* v_body_1252_; uint8_t v_binderInfo_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_binderName_1250_ = lean_ctor_get(v_e_1242_, 0);
lean_inc(v_binderName_1250_);
v_binderType_1251_ = lean_ctor_get(v_e_1242_, 1);
lean_inc_ref(v_binderType_1251_);
v_body_1252_ = lean_ctor_get(v_e_1242_, 2);
lean_inc_ref(v_body_1252_);
v_binderInfo_1253_ = lean_ctor_get_uint8(v_e_1242_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1242_, 3);
v___x_1254_ = lean_expr_instantiate_rev(v_binderType_1251_, v_fvars_1241_);
lean_dec_ref(v_binderType_1251_);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1236_);
v___x_1255_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1254_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_fst_1257_ = lean_ctor_get(v_a_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v_a_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec(v_a_1256_);
v___x_1259_ = lean_box(v_usedLetOnly_1238_);
v___x_1260_ = lean_box(v_skipConstInApp_1239_);
v___x_1261_ = lean_box(v_skipInstances_1240_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1262_, 0, v_fvars_1241_);
lean_closure_set(v___f_1262_, 1, v_pre_1236_);
lean_closure_set(v___f_1262_, 2, v_post_1237_);
lean_closure_set(v___f_1262_, 3, v___x_1259_);
lean_closure_set(v___f_1262_, 4, v___x_1260_);
lean_closure_set(v___f_1262_, 5, v___x_1261_);
lean_closure_set(v___f_1262_, 6, v_body_1252_);
v___x_1263_ = 0;
v___x_1264_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1250_, v_binderInfo_1253_, v_fst_1257_, v___f_1262_, v___x_1263_, v_a_1243_, v_snd_1258_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1264_;
}
else
{
lean_dec_ref(v_body_1252_);
lean_dec(v_binderName_1250_);
lean_dec_ref(v_fvars_1241_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
return v___x_1255_;
}
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_expr_instantiate_rev(v_e_1242_, v_fvars_1241_);
lean_dec_ref(v_e_1242_);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1236_);
v___x_1266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v___x_1265_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; uint8_t v___x_1270_; uint8_t v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_fst_1268_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_fst_1268_);
v_snd_1269_ = lean_ctor_get(v_a_1267_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_a_1267_);
v___x_1270_ = 0;
v___x_1271_ = 1;
v___x_1272_ = 1;
v___x_1273_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1241_, v_fst_1268_, v___x_1270_, v_usedLetOnly_1238_, v___x_1270_, v___x_1271_, v___x_1272_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v_fvars_1241_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1240_, v_a_1274_, v_a_1243_, v_snd_1269_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1275_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_snd_1269_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
v_a_1276_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1273_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1241_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1284_, lean_object* v_pre_1285_, lean_object* v_post_1286_, uint8_t v_usedLetOnly_1287_, uint8_t v_skipConstInApp_1288_, uint8_t v_skipInstances_1289_, lean_object* v_body_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_array_push(v_fvars_1284_, v_x_1291_);
v___x_1300_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1285_, v_post_1286_, v_usedLetOnly_1287_, v_skipConstInApp_1288_, v_skipInstances_1289_, v___x_1299_, v_body_1290_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1301_, lean_object* v_pre_1302_, lean_object* v_post_1303_, lean_object* v_usedLetOnly_1304_, lean_object* v_skipConstInApp_1305_, lean_object* v_skipInstances_1306_, lean_object* v_body_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_usedLetOnly_boxed_1316_; uint8_t v_skipConstInApp_boxed_1317_; uint8_t v_skipInstances_boxed_1318_; lean_object* v_res_1319_; 
v_usedLetOnly_boxed_1316_ = lean_unbox(v_usedLetOnly_1304_);
v_skipConstInApp_boxed_1317_ = lean_unbox(v_skipConstInApp_1305_);
v_skipInstances_boxed_1318_ = lean_unbox(v_skipInstances_1306_);
v_res_1319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1301_, v_pre_1302_, v_post_1303_, v_usedLetOnly_boxed_1316_, v_skipConstInApp_boxed_1317_, v_skipInstances_boxed_1318_, v_body_1307_, v_x_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1309_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1320_, lean_object* v_post_1321_, uint8_t v_usedLetOnly_1322_, uint8_t v_skipConstInApp_1323_, uint8_t v_skipInstances_1324_, lean_object* v_fvars_1325_, lean_object* v_e_1326_, lean_object* v_a_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
if (lean_obj_tag(v_e_1326_) == 8)
{
lean_object* v_declName_1334_; lean_object* v_type_1335_; lean_object* v_value_1336_; lean_object* v_body_1337_; uint8_t v_nondep_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_declName_1334_ = lean_ctor_get(v_e_1326_, 0);
lean_inc(v_declName_1334_);
v_type_1335_ = lean_ctor_get(v_e_1326_, 1);
lean_inc_ref(v_type_1335_);
v_value_1336_ = lean_ctor_get(v_e_1326_, 2);
lean_inc_ref(v_value_1336_);
v_body_1337_ = lean_ctor_get(v_e_1326_, 3);
lean_inc_ref(v_body_1337_);
v_nondep_1338_ = lean_ctor_get_uint8(v_e_1326_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1326_, 4);
v___x_1339_ = lean_expr_instantiate_rev(v_type_1335_, v_fvars_1325_);
lean_dec_ref(v_type_1335_);
lean_inc_ref(v_post_1321_);
lean_inc_ref(v_pre_1320_);
v___x_1340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1320_, v_post_1321_, v_usedLetOnly_1322_, v_skipConstInApp_1323_, v_skipInstances_1324_, v___x_1339_, v_a_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v_fst_1342_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_fst_1342_);
v_snd_1343_ = lean_ctor_get(v_a_1341_, 1);
lean_inc(v_snd_1343_);
lean_dec(v_a_1341_);
v___x_1344_ = lean_expr_instantiate_rev(v_value_1336_, v_fvars_1325_);
lean_dec_ref(v_value_1336_);
lean_inc_ref(v_post_1321_);
lean_inc_ref(v_pre_1320_);
v___x_1345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1320_, v_post_1321_, v_usedLetOnly_1322_, v_skipConstInApp_1323_, v_skipInstances_1324_, v___x_1344_, v_a_1327_, v_snd_1343_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___f_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_fst_1347_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_fst_1347_);
v_snd_1348_ = lean_ctor_get(v_a_1346_, 1);
lean_inc(v_snd_1348_);
lean_dec(v_a_1346_);
v___x_1349_ = lean_box(v_usedLetOnly_1322_);
v___x_1350_ = lean_box(v_skipConstInApp_1323_);
v___x_1351_ = lean_box(v_skipInstances_1324_);
v___f_1352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1352_, 0, v_fvars_1325_);
lean_closure_set(v___f_1352_, 1, v_pre_1320_);
lean_closure_set(v___f_1352_, 2, v_post_1321_);
lean_closure_set(v___f_1352_, 3, v___x_1349_);
lean_closure_set(v___f_1352_, 4, v___x_1350_);
lean_closure_set(v___f_1352_, 5, v___x_1351_);
lean_closure_set(v___f_1352_, 6, v_body_1337_);
v___x_1353_ = 0;
v___x_1354_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1334_, v_fst_1342_, v_fst_1347_, v___f_1352_, v_nondep_1338_, v___x_1353_, v_a_1327_, v_snd_1348_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1354_;
}
else
{
lean_dec(v_fst_1342_);
lean_dec_ref(v_body_1337_);
lean_dec(v_declName_1334_);
lean_dec_ref(v_fvars_1325_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
return v___x_1345_;
}
}
else
{
lean_dec_ref(v_body_1337_);
lean_dec_ref(v_value_1336_);
lean_dec(v_declName_1334_);
lean_dec_ref(v_fvars_1325_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
return v___x_1340_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_expr_instantiate_rev(v_e_1326_, v_fvars_1325_);
lean_dec_ref(v_e_1326_);
lean_inc_ref(v_post_1321_);
lean_inc_ref(v_pre_1320_);
v___x_1356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1320_, v_post_1321_, v_usedLetOnly_1322_, v_skipConstInApp_1323_, v_skipInstances_1324_, v___x_1355_, v_a_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; uint8_t v___x_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v_fst_1358_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_fst_1358_);
v_snd_1359_ = lean_ctor_get(v_a_1357_, 1);
lean_inc(v_snd_1359_);
lean_dec(v_a_1357_);
v___x_1360_ = 0;
v___x_1361_ = 1;
v___x_1362_ = l_Lean_Meta_mkLetFVars(v_fvars_1325_, v_fst_1358_, v_usedLetOnly_1322_, v___x_1360_, v___x_1361_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v_fvars_1325_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1320_, v_post_1321_, v_usedLetOnly_1322_, v_skipConstInApp_1323_, v_skipInstances_1324_, v_a_1363_, v_a_1327_, v_snd_1359_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1364_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_snd_1359_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
v_a_1365_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1362_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1325_);
lean_dec_ref(v_post_1321_);
lean_dec_ref(v_pre_1320_);
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1373_, lean_object* v_post_1374_, uint8_t v_usedLetOnly_1375_, uint8_t v_skipConstInApp_1376_, uint8_t v_skipInstances_1377_, size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_bs_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1379_, v_sz_1378_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v_post_1374_);
lean_dec_ref(v_pre_1373_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_bs_1380_);
lean_ctor_set(v___x_1389_, 1, v___y_1382_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v_v_1391_; lean_object* v___x_1392_; 
v_v_1391_ = lean_array_uget_borrowed(v_bs_1380_, v_i_1379_);
lean_inc(v_v_1391_);
lean_inc_ref(v_post_1374_);
lean_inc_ref(v_pre_1373_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1373_, v_post_1374_, v_usedLetOnly_1375_, v_skipConstInApp_1376_, v_skipInstances_1377_, v_v_1391_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1396_; lean_object* v_bs_x27_1397_; size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_fst_1394_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_fst_1394_);
v_snd_1395_ = lean_ctor_get(v_a_1393_, 1);
lean_inc(v_snd_1395_);
lean_dec(v_a_1393_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v_bs_x27_1397_ = lean_array_uset(v_bs_1380_, v_i_1379_, v___x_1396_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1379_, v___x_1398_);
v___x_1400_ = lean_array_uset(v_bs_x27_1397_, v_i_1379_, v_fst_1394_);
v_i_1379_ = v___x_1399_;
v_bs_1380_ = v___x_1400_;
v___y_1382_ = v_snd_1395_;
goto _start;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v_bs_1380_);
lean_dec_ref(v_post_1374_);
lean_dec_ref(v_pre_1373_);
v_a_1402_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1392_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1410_, lean_object* v_post_1411_, uint8_t v_usedLetOnly_1412_, uint8_t v_skipConstInApp_1413_, uint8_t v_skipInstances_1414_, lean_object* v___x_1415_, lean_object* v___y_1416_, lean_object* v_b_1417_, lean_object* v_a_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1410_, v_post_1411_, v_usedLetOnly_1412_, v_skipConstInApp_1413_, v_skipInstances_1414_, v___x_1415_, v___y_1416_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1444_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1444_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1444_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1443_; 
v_fst_1430_ = lean_ctor_get(v_a_1426_, 0);
v_snd_1431_ = lean_ctor_get(v_a_1426_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_a_1426_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1433_ = v_a_1426_;
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_snd_1431_);
lean_inc(v_fst_1430_);
lean_dec(v_a_1426_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1435_ = lean_array_fset(v_b_1417_, v_a_1418_, v_fst_1430_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1436_);
v___x_1438_ = v___x_1433_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1431_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1438_);
v___x_1440_ = v___x_1428_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_b_1417_);
v_a_1445_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1425_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1425_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1453_, lean_object* v_post_1454_, lean_object* v_usedLetOnly_1455_, lean_object* v_skipConstInApp_1456_, lean_object* v_skipInstances_1457_, lean_object* v___x_1458_, lean_object* v___y_1459_, lean_object* v_b_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_usedLetOnly_boxed_1468_; uint8_t v_skipConstInApp_boxed_1469_; uint8_t v_skipInstances_boxed_1470_; lean_object* v_res_1471_; 
v_usedLetOnly_boxed_1468_ = lean_unbox(v_usedLetOnly_1455_);
v_skipConstInApp_boxed_1469_ = lean_unbox(v_skipConstInApp_1456_);
v_skipInstances_boxed_1470_ = lean_unbox(v_skipInstances_1457_);
v_res_1471_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1453_, v_post_1454_, v_usedLetOnly_boxed_1468_, v_skipConstInApp_boxed_1469_, v_skipInstances_boxed_1470_, v___x_1458_, v___y_1459_, v_b_1460_, v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v_a_1461_);
lean_dec(v___y_1459_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1472_, lean_object* v___x_1473_, lean_object* v_pre_1474_, lean_object* v_post_1475_, uint8_t v_usedLetOnly_1476_, uint8_t v_skipConstInApp_1477_, uint8_t v_skipInstances_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___y_1489_; uint8_t v___x_1523_; 
v___x_1523_ = lean_nat_dec_lt(v_a_1479_, v_upperBound_1472_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_a_1479_);
lean_dec_ref(v_post_1475_);
lean_dec_ref(v_pre_1474_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_b_1480_);
lean_ctor_set(v___x_1524_, 1, v___y_1482_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_array_fget_borrowed(v_b_1480_, v_a_1479_);
v___x_1527_ = lean_array_get_size(v___x_1473_);
v___x_1528_ = lean_nat_dec_lt(v_a_1479_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; 
lean_inc(v___x_1526_);
v___x_1529_ = lean_box(v_usedLetOnly_1476_);
v___x_1530_ = lean_box(v_skipConstInApp_1477_);
v___x_1531_ = lean_box(v_skipInstances_1478_);
lean_inc(v_a_1479_);
lean_inc(v___y_1481_);
lean_inc_ref(v_post_1475_);
lean_inc_ref(v_pre_1474_);
v___f_1532_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1532_, 0, v_pre_1474_);
lean_closure_set(v___f_1532_, 1, v_post_1475_);
lean_closure_set(v___f_1532_, 2, v___x_1529_);
lean_closure_set(v___f_1532_, 3, v___x_1530_);
lean_closure_set(v___f_1532_, 4, v___x_1531_);
lean_closure_set(v___f_1532_, 5, v___x_1526_);
lean_closure_set(v___f_1532_, 6, v___y_1481_);
lean_closure_set(v___f_1532_, 7, v_b_1480_);
lean_closure_set(v___f_1532_, 8, v_a_1479_);
v___y_1489_ = v___f_1532_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1533_; uint8_t v_isInstance_1534_; 
v___x_1533_ = lean_array_fget_borrowed(v___x_1473_, v_a_1479_);
v_isInstance_1534_ = lean_ctor_get_uint8(v___x_1533_, sizeof(void*)*1 + 4);
if (v_isInstance_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; 
lean_inc(v___x_1526_);
v___x_1535_ = lean_box(v_usedLetOnly_1476_);
v___x_1536_ = lean_box(v_skipConstInApp_1477_);
v___x_1537_ = lean_box(v_skipInstances_1478_);
lean_inc(v_a_1479_);
lean_inc(v___y_1481_);
lean_inc_ref(v_post_1475_);
lean_inc_ref(v_pre_1474_);
v___f_1538_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1538_, 0, v_pre_1474_);
lean_closure_set(v___f_1538_, 1, v_post_1475_);
lean_closure_set(v___f_1538_, 2, v___x_1535_);
lean_closure_set(v___f_1538_, 3, v___x_1536_);
lean_closure_set(v___f_1538_, 4, v___x_1537_);
lean_closure_set(v___f_1538_, 5, v___x_1526_);
lean_closure_set(v___f_1538_, 6, v___y_1481_);
lean_closure_set(v___f_1538_, 7, v_b_1480_);
lean_closure_set(v___f_1538_, 8, v_a_1479_);
v___y_1489_ = v___f_1538_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1539_; lean_object* v___f_1540_; 
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_b_1480_);
v___f_1540_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1540_, 0, v___x_1539_);
v___y_1489_ = v___f_1540_;
goto v___jp_1488_;
}
}
}
v___jp_1488_:
{
lean_object* v___x_1490_; 
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
v___x_1490_ = lean_apply_6(v___y_1489_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, lean_box(0));
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1514_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_fst_1495_; 
v_fst_1495_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_fst_1495_);
if (lean_obj_tag(v_fst_1495_) == 0)
{
lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1479_);
lean_dec_ref(v_post_1475_);
lean_dec_ref(v_pre_1474_);
v_snd_1496_ = lean_ctor_get(v_a_1491_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_a_1491_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_a_1491_, 0);
lean_dec(v_unused_1508_);
v___x_1498_ = v_a_1491_;
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_dec(v_a_1491_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_a_1500_; lean_object* v___x_1502_; 
v_a_1500_ = lean_ctor_get(v_fst_1495_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v_fst_1495_, 1);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v_a_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_snd_1496_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1502_);
v___x_1504_ = v___x_1493_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_snd_1509_; lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_del_object(v___x_1493_);
v_snd_1509_ = lean_ctor_get(v_a_1491_, 1);
lean_inc(v_snd_1509_);
lean_dec(v_a_1491_);
v_a_1510_ = lean_ctor_get(v_fst_1495_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_fst_1495_, 1);
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_add(v_a_1479_, v___x_1511_);
lean_dec(v_a_1479_);
v_a_1479_ = v___x_1512_;
v_b_1480_ = v_a_1510_;
v___y_1482_ = v_snd_1509_;
goto _start;
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_a_1479_);
lean_dec_ref(v_post_1475_);
lean_dec_ref(v_pre_1474_);
v_a_1515_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1490_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1490_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1541_, lean_object* v_pre_1542_, lean_object* v_post_1543_, uint8_t v_usedLetOnly_1544_, uint8_t v_skipConstInApp_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_f_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; 
if (lean_obj_tag(v_x_1546_) == 5)
{
lean_object* v_fn_1612_; lean_object* v_arg_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_fn_1612_ = lean_ctor_get(v_x_1546_, 0);
lean_inc_ref(v_fn_1612_);
v_arg_1613_ = lean_ctor_get(v_x_1546_, 1);
lean_inc_ref(v_arg_1613_);
lean_dec_ref_known(v_x_1546_, 2);
v___x_1614_ = lean_array_set(v_x_1547_, v_x_1548_, v_arg_1613_);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_sub(v_x_1548_, v___x_1615_);
lean_dec(v_x_1548_);
v_x_1546_ = v_fn_1612_;
v_x_1547_ = v___x_1614_;
v_x_1548_ = v___x_1616_;
goto _start;
}
else
{
lean_dec(v_x_1548_);
if (v_skipConstInApp_1545_ == 0)
{
goto v___jp_1607_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = l_Lean_Expr_isConst(v_x_1546_);
if (v___x_1618_ == 0)
{
goto v___jp_1607_;
}
else
{
v_f_1557_ = v_x_1546_;
v___y_1558_ = v___y_1549_;
v___y_1559_ = v___y_1550_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
v___y_1563_ = v___y_1554_;
goto v___jp_1556_;
}
}
}
v___jp_1556_:
{
if (v_skipInstances_1541_ == 0)
{
size_t v_sz_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v_sz_1564_ = lean_array_size(v_x_1547_);
v___x_1565_ = ((size_t)0ULL);
lean_inc_ref(v_post_1543_);
lean_inc_ref(v_pre_1542_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1542_, v_post_1543_, v_usedLetOnly_1544_, v_skipConstInApp_1545_, v_skipInstances_1541_, v_sz_1564_, v___x_1565_, v_x_1547_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v_fst_1568_ = lean_ctor_get(v_a_1567_, 0);
lean_inc(v_fst_1568_);
v_snd_1569_ = lean_ctor_get(v_a_1567_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_a_1567_);
v___x_1570_ = l_Lean_mkAppN(v_f_1557_, v_fst_1568_);
lean_dec(v_fst_1568_);
v___x_1571_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1542_, v_post_1543_, v_usedLetOnly_1544_, v_skipConstInApp_1545_, v_skipInstances_1541_, v___x_1570_, v___y_1558_, v_snd_1569_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1571_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v_f_1557_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
v_a_1572_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1566_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1566_);
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
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_array_get_size(v_x_1547_);
lean_inc_ref(v_f_1557_);
v___x_1581_ = l_Lean_Meta_getFunInfoNArgs(v_f_1557_, v___x_1580_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v_paramInfo_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v_paramInfo_1583_ = lean_ctor_get(v_a_1582_, 0);
lean_inc_ref(v_paramInfo_1583_);
lean_dec(v_a_1582_);
v___x_1584_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1543_);
lean_inc_ref(v_pre_1542_);
v___x_1585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1580_, v_paramInfo_1583_, v_pre_1542_, v_post_1543_, v_usedLetOnly_1544_, v_skipConstInApp_1545_, v_skipInstances_1541_, v___x_1584_, v_x_1547_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec_ref(v_paramInfo_1583_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v_fst_1587_; lean_object* v_snd_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v_fst_1587_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_fst_1587_);
v_snd_1588_ = lean_ctor_get(v_a_1586_, 1);
lean_inc(v_snd_1588_);
lean_dec(v_a_1586_);
v___x_1589_ = l_Lean_mkAppN(v_f_1557_, v_fst_1587_);
lean_dec(v_fst_1587_);
v___x_1590_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1542_, v_post_1543_, v_usedLetOnly_1544_, v_skipConstInApp_1545_, v_skipInstances_1541_, v___x_1589_, v___y_1558_, v_snd_1588_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1590_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_f_1557_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
v_a_1591_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1585_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1585_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v___y_1559_);
lean_dec_ref(v_f_1557_);
lean_dec_ref(v_x_1547_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
v_a_1599_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1581_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1581_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
v___jp_1607_:
{
lean_object* v___x_1608_; 
lean_inc_ref(v_post_1543_);
lean_inc_ref(v_pre_1542_);
v___x_1608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1542_, v_post_1543_, v_usedLetOnly_1544_, v_skipConstInApp_1545_, v_skipInstances_1541_, v_x_1546_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v_fst_1610_; lean_object* v_snd_1611_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_fst_1610_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_fst_1610_);
v_snd_1611_ = lean_ctor_get(v_a_1609_, 1);
lean_inc(v_snd_1611_);
lean_dec(v_a_1609_);
v_f_1557_ = v_fst_1610_;
v___y_1558_ = v___y_1549_;
v___y_1559_ = v_snd_1611_;
v___y_1560_ = v___y_1551_;
v___y_1561_ = v___y_1552_;
v___y_1562_ = v___y_1553_;
v___y_1563_ = v___y_1554_;
goto v___jp_1556_;
}
else
{
lean_dec_ref(v_x_1547_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1619_, lean_object* v_pre_1620_, lean_object* v_e_1621_, lean_object* v_post_1622_, uint8_t v_usedLetOnly_1623_, uint8_t v_skipConstInApp_1624_, uint8_t v_skipInstances_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Core_checkSystem(v___x_1619_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1633_, 1);
lean_inc_ref(v_pre_1620_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc_ref(v_e_1621_);
v___x_1634_ = lean_apply_7(v_pre_1620_, v_e_1621_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, lean_box(0));
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1696_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1696_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1696_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1695_; 
v_fst_1639_ = lean_ctor_get(v_a_1635_, 0);
v_snd_1640_ = lean_ctor_get(v_a_1635_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1642_ = v_a_1635_;
v_isShared_1643_ = v_isSharedCheck_1695_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_snd_1640_);
lean_inc(v_fst_1639_);
lean_dec(v_a_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1695_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___y_1645_; 
switch(lean_obj_tag(v_fst_1639_))
{
case 0:
{
lean_object* v_e_1684_; lean_object* v___x_1686_; 
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_e_1621_);
lean_dec_ref(v_pre_1620_);
v_e_1684_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc_ref(v_e_1684_);
lean_dec_ref_known(v_fst_1639_, 1);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v_e_1684_);
v___x_1686_ = v___x_1642_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_e_1684_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_snd_1640_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1686_);
v___x_1688_ = v___x_1637_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
case 1:
{
lean_object* v_e_1691_; lean_object* v___x_1692_; 
lean_del_object(v___x_1642_);
lean_del_object(v___x_1637_);
lean_dec_ref(v_e_1621_);
v_e_1691_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc_ref(v_e_1691_);
lean_dec_ref_known(v_fst_1639_, 1);
v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v_e_1691_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1692_;
}
default: 
{
lean_object* v_e_x3f_1693_; 
lean_del_object(v___x_1642_);
lean_del_object(v___x_1637_);
v_e_x3f_1693_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc(v_e_x3f_1693_);
lean_dec_ref_known(v_fst_1639_, 1);
if (lean_obj_tag(v_e_x3f_1693_) == 0)
{
v___y_1645_ = v_e_1621_;
goto v___jp_1644_;
}
else
{
lean_object* v_val_1694_; 
lean_dec_ref(v_e_1621_);
v_val_1694_ = lean_ctor_get(v_e_x3f_1693_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v_e_x3f_1693_, 1);
v___y_1645_ = v_val_1694_;
goto v___jp_1644_;
}
}
}
v___jp_1644_:
{
switch(lean_obj_tag(v___y_1645_))
{
case 7:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1647_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1646_, v___y_1645_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1647_;
}
case 6:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1648_, v___y_1645_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1649_;
}
case 8:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1650_, v___y_1645_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1651_;
}
case 5:
{
lean_object* v_dummy_1652_; lean_object* v_nargs_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_dummy_1652_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1653_ = l_Lean_Expr_getAppNumArgs(v___y_1645_);
lean_inc(v_nargs_1653_);
v___x_1654_ = lean_mk_array(v_nargs_1653_, v_dummy_1652_);
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_nat_sub(v_nargs_1653_, v___x_1655_);
lean_dec(v_nargs_1653_);
v___x_1657_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1625_, v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v___y_1645_, v___x_1654_, v___x_1656_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1657_;
}
case 10:
{
lean_object* v_data_1658_; lean_object* v_expr_1659_; lean_object* v___x_1660_; 
v_data_1658_ = lean_ctor_get(v___y_1645_, 0);
v_expr_1659_ = lean_ctor_get(v___y_1645_, 1);
lean_inc_ref(v_expr_1659_);
lean_inc_ref(v_post_1622_);
lean_inc_ref(v_pre_1620_);
v___x_1660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v_expr_1659_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; size_t v___x_1664_; size_t v___x_1665_; uint8_t v___x_1666_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v_fst_1662_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v_a_1661_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_a_1661_);
v___x_1664_ = lean_ptr_addr(v_expr_1659_);
v___x_1665_ = lean_ptr_addr(v_fst_1662_);
v___x_1666_ = lean_usize_dec_eq(v___x_1664_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_inc(v_data_1658_);
lean_dec_ref_known(v___y_1645_, 2);
v___x_1667_ = l_Lean_Expr_mdata___override(v_data_1658_, v_fst_1662_);
v___x_1668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1667_, v___y_1626_, v_snd_1663_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; 
lean_dec(v_fst_1662_);
v___x_1669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___y_1645_, v___y_1626_, v_snd_1663_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1669_;
}
}
else
{
lean_dec_ref_known(v___y_1645_, 2);
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_pre_1620_);
return v___x_1660_;
}
}
case 11:
{
lean_object* v_typeName_1670_; lean_object* v_idx_1671_; lean_object* v_struct_1672_; lean_object* v___x_1673_; 
v_typeName_1670_ = lean_ctor_get(v___y_1645_, 0);
v_idx_1671_ = lean_ctor_get(v___y_1645_, 1);
v_struct_1672_ = lean_ctor_get(v___y_1645_, 2);
lean_inc_ref(v_struct_1672_);
lean_inc_ref(v_post_1622_);
lean_inc_ref(v_pre_1620_);
v___x_1673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v_struct_1672_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v_fst_1675_; lean_object* v_snd_1676_; size_t v___x_1677_; size_t v___x_1678_; uint8_t v___x_1679_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_fst_1675_ = lean_ctor_get(v_a_1674_, 0);
lean_inc(v_fst_1675_);
v_snd_1676_ = lean_ctor_get(v_a_1674_, 1);
lean_inc(v_snd_1676_);
lean_dec(v_a_1674_);
v___x_1677_ = lean_ptr_addr(v_struct_1672_);
v___x_1678_ = lean_ptr_addr(v_fst_1675_);
v___x_1679_ = lean_usize_dec_eq(v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_inc(v_idx_1671_);
lean_inc(v_typeName_1670_);
lean_dec_ref_known(v___y_1645_, 3);
v___x_1680_ = l_Lean_Expr_proj___override(v_typeName_1670_, v_idx_1671_, v_fst_1675_);
v___x_1681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1680_, v___y_1626_, v_snd_1676_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
lean_dec(v_fst_1675_);
v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___y_1645_, v___y_1626_, v_snd_1676_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1682_;
}
}
else
{
lean_dec_ref_known(v___y_1645_, 3);
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_pre_1620_);
return v___x_1673_;
}
}
default: 
{
lean_object* v___x_1683_; 
v___x_1683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1620_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___y_1645_, v___y_1626_, v_snd_1640_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1683_;
}
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_e_1621_);
lean_dec_ref(v_pre_1620_);
v_a_1697_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1634_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1634_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v___y_1627_);
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_e_1621_);
lean_dec_ref(v_pre_1620_);
v_a_1705_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1633_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1633_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1713_, lean_object* v_pre_1714_, lean_object* v_e_1715_, lean_object* v_post_1716_, lean_object* v_usedLetOnly_1717_, lean_object* v_skipConstInApp_1718_, lean_object* v_skipInstances_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_usedLetOnly_boxed_1727_; uint8_t v_skipConstInApp_boxed_1728_; uint8_t v_skipInstances_boxed_1729_; lean_object* v_res_1730_; 
v_usedLetOnly_boxed_1727_ = lean_unbox(v_usedLetOnly_1717_);
v_skipConstInApp_boxed_1728_ = lean_unbox(v_skipConstInApp_1718_);
v_skipInstances_boxed_1729_ = lean_unbox(v_skipInstances_1719_);
v_res_1730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1713_, v_pre_1714_, v_e_1715_, v_post_1716_, v_usedLetOnly_boxed_1727_, v_skipConstInApp_boxed_1728_, v_skipInstances_boxed_1729_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1720_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1731_, lean_object* v_post_1732_, uint8_t v_usedLetOnly_1733_, uint8_t v_skipConstInApp_1734_, uint8_t v_skipInstances_1735_, lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_inc(v_a_1737_);
v___x_1744_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1744_, 0, lean_box(0));
lean_closure_set(v___x_1744_, 1, lean_box(0));
lean_closure_set(v___x_1744_, 2, v_a_1737_);
v___x_1745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1744_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1800_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1800_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1800_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1799_; 
v_fst_1750_ = lean_ctor_get(v_a_1746_, 0);
v_snd_1751_ = lean_ctor_get(v_a_1746_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_a_1746_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1753_ = v_a_1746_;
v_isShared_1754_ = v_isSharedCheck_1799_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snd_1751_);
lean_inc(v_fst_1750_);
lean_dec(v_a_1746_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1799_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1750_, v_e_1736_);
lean_dec(v_fst_1750_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1753_);
lean_del_object(v___x_1748_);
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1757_ = lean_box(v_usedLetOnly_1733_);
v___x_1758_ = lean_box(v_skipConstInApp_1734_);
v___x_1759_ = lean_box(v_skipInstances_1735_);
lean_inc_ref(v_e_1736_);
v___f_1760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1760_, 0, v___x_1756_);
lean_closure_set(v___f_1760_, 1, v_pre_1731_);
lean_closure_set(v___f_1760_, 2, v_e_1736_);
lean_closure_set(v___f_1760_, 3, v_post_1732_);
lean_closure_set(v___f_1760_, 4, v___x_1757_);
lean_closure_set(v___f_1760_, 5, v___x_1758_);
lean_closure_set(v___f_1760_, 6, v___x_1759_);
v___x_1761_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1760_, v_a_1737_, v_snd_1751_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_fst_1763_ = lean_ctor_get(v_a_1762_, 0);
lean_inc_n(v_fst_1763_, 2);
v_snd_1764_ = lean_ctor_get(v_a_1762_, 1);
lean_inc(v_snd_1764_);
lean_dec(v_a_1762_);
lean_inc(v_a_1737_);
v___f_1765_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1765_, 0, v_a_1737_);
lean_closure_set(v___f_1765_, 1, v_e_1736_);
lean_closure_set(v___f_1765_, 2, v_fst_1763_);
v___x_1766_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1765_, v_snd_1764_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1783_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
v_snd_1771_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v_a_1767_, 0);
lean_dec(v_unused_1782_);
v___x_1773_ = v_a_1767_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_dec(v_a_1767_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v_fst_1763_);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_fst_1763_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_snd_1771_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1776_);
v___x_1778_ = v___x_1769_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_fst_1763_);
v_a_1784_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1766_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1766_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_dec_ref(v_e_1736_);
return v___x_1761_;
}
}
else
{
lean_object* v_val_1792_; lean_object* v___x_1794_; 
lean_dec_ref(v_e_1736_);
lean_dec_ref(v_post_1732_);
lean_dec_ref(v_pre_1731_);
v_val_1792_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1755_, 1);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v_val_1792_);
v___x_1794_ = v___x_1753_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_val_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_snd_1751_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1794_);
v___x_1796_ = v___x_1748_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_e_1736_);
lean_dec_ref(v_post_1732_);
lean_dec_ref(v_pre_1731_);
v_a_1801_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1745_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1745_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1809_, lean_object* v_pre_1810_, lean_object* v_post_1811_, lean_object* v_usedLetOnly_1812_, lean_object* v_skipConstInApp_1813_, lean_object* v_skipInstances_1814_, lean_object* v_body_1815_, lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_usedLetOnly_boxed_1824_; uint8_t v_skipConstInApp_boxed_1825_; uint8_t v_skipInstances_boxed_1826_; lean_object* v_res_1827_; 
v_usedLetOnly_boxed_1824_ = lean_unbox(v_usedLetOnly_1812_);
v_skipConstInApp_boxed_1825_ = lean_unbox(v_skipConstInApp_1813_);
v_skipInstances_boxed_1826_ = lean_unbox(v_skipInstances_1814_);
v_res_1827_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1809_, v_pre_1810_, v_post_1811_, v_usedLetOnly_boxed_1824_, v_skipConstInApp_boxed_1825_, v_skipInstances_boxed_1826_, v_body_1815_, v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1817_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1828_, lean_object* v_post_1829_, uint8_t v_usedLetOnly_1830_, uint8_t v_skipConstInApp_1831_, uint8_t v_skipInstances_1832_, lean_object* v_fvars_1833_, lean_object* v_e_1834_, lean_object* v_a_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
if (lean_obj_tag(v_e_1834_) == 7)
{
lean_object* v_binderName_1842_; lean_object* v_binderType_1843_; lean_object* v_body_1844_; uint8_t v_binderInfo_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_binderName_1842_ = lean_ctor_get(v_e_1834_, 0);
lean_inc(v_binderName_1842_);
v_binderType_1843_ = lean_ctor_get(v_e_1834_, 1);
lean_inc_ref(v_binderType_1843_);
v_body_1844_ = lean_ctor_get(v_e_1834_, 2);
lean_inc_ref(v_body_1844_);
v_binderInfo_1845_ = lean_ctor_get_uint8(v_e_1834_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1834_, 3);
v___x_1846_ = lean_expr_instantiate_rev(v_binderType_1843_, v_fvars_1833_);
lean_dec_ref(v_binderType_1843_);
lean_inc_ref(v_post_1829_);
lean_inc_ref(v_pre_1828_);
v___x_1847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1828_, v_post_1829_, v_usedLetOnly_1830_, v_skipConstInApp_1831_, v_skipInstances_1832_, v___x_1846_, v_a_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___f_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v_fst_1849_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_fst_1849_);
v_snd_1850_ = lean_ctor_get(v_a_1848_, 1);
lean_inc(v_snd_1850_);
lean_dec(v_a_1848_);
v___x_1851_ = lean_box(v_usedLetOnly_1830_);
v___x_1852_ = lean_box(v_skipConstInApp_1831_);
v___x_1853_ = lean_box(v_skipInstances_1832_);
v___f_1854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1854_, 0, v_fvars_1833_);
lean_closure_set(v___f_1854_, 1, v_pre_1828_);
lean_closure_set(v___f_1854_, 2, v_post_1829_);
lean_closure_set(v___f_1854_, 3, v___x_1851_);
lean_closure_set(v___f_1854_, 4, v___x_1852_);
lean_closure_set(v___f_1854_, 5, v___x_1853_);
lean_closure_set(v___f_1854_, 6, v_body_1844_);
v___x_1855_ = 0;
v___x_1856_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1842_, v_binderInfo_1845_, v_fst_1849_, v___f_1854_, v___x_1855_, v_a_1835_, v_snd_1850_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1856_;
}
else
{
lean_dec_ref(v_body_1844_);
lean_dec(v_binderName_1842_);
lean_dec_ref(v_fvars_1833_);
lean_dec_ref(v_post_1829_);
lean_dec_ref(v_pre_1828_);
return v___x_1847_;
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_expr_instantiate_rev(v_e_1834_, v_fvars_1833_);
lean_dec_ref(v_e_1834_);
lean_inc_ref(v_post_1829_);
lean_inc_ref(v_pre_1828_);
v___x_1858_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1828_, v_post_1829_, v_usedLetOnly_1830_, v_skipConstInApp_1831_, v_skipInstances_1832_, v___x_1857_, v_a_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; uint8_t v___x_1862_; uint8_t v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v_fst_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_fst_1860_);
v_snd_1861_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_a_1859_);
v___x_1862_ = 0;
v___x_1863_ = 1;
v___x_1864_ = 1;
v___x_1865_ = l_Lean_Meta_mkForallFVars(v_fvars_1833_, v_fst_1860_, v___x_1862_, v_usedLetOnly_1830_, v___x_1863_, v___x_1864_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec_ref(v_fvars_1833_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1828_, v_post_1829_, v_usedLetOnly_1830_, v_skipConstInApp_1831_, v_skipInstances_1832_, v_a_1866_, v_a_1835_, v_snd_1861_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1867_;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_snd_1861_);
lean_dec_ref(v_post_1829_);
lean_dec_ref(v_pre_1828_);
v_a_1868_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1865_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1865_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1833_);
lean_dec_ref(v_post_1829_);
lean_dec_ref(v_pre_1828_);
return v___x_1858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1876_, lean_object* v_pre_1877_, lean_object* v_post_1878_, uint8_t v_usedLetOnly_1879_, uint8_t v_skipConstInApp_1880_, uint8_t v_skipInstances_1881_, lean_object* v_body_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_array_push(v_fvars_1876_, v_x_1883_);
v___x_1892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1877_, v_post_1878_, v_usedLetOnly_1879_, v_skipConstInApp_1880_, v_skipInstances_1881_, v___x_1891_, v_body_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1893_, lean_object* v_post_1894_, lean_object* v_usedLetOnly_1895_, lean_object* v_skipConstInApp_1896_, lean_object* v_skipInstances_1897_, lean_object* v_sz_1898_, lean_object* v_i_1899_, lean_object* v_bs_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
uint8_t v_usedLetOnly_boxed_1908_; uint8_t v_skipConstInApp_boxed_1909_; uint8_t v_skipInstances_boxed_1910_; size_t v_sz_boxed_1911_; size_t v_i_boxed_1912_; lean_object* v_res_1913_; 
v_usedLetOnly_boxed_1908_ = lean_unbox(v_usedLetOnly_1895_);
v_skipConstInApp_boxed_1909_ = lean_unbox(v_skipConstInApp_1896_);
v_skipInstances_boxed_1910_ = lean_unbox(v_skipInstances_1897_);
v_sz_boxed_1911_ = lean_unbox_usize(v_sz_1898_);
lean_dec(v_sz_1898_);
v_i_boxed_1912_ = lean_unbox_usize(v_i_1899_);
lean_dec(v_i_1899_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1893_, v_post_1894_, v_usedLetOnly_boxed_1908_, v_skipConstInApp_boxed_1909_, v_skipInstances_boxed_1910_, v_sz_boxed_1911_, v_i_boxed_1912_, v_bs_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1901_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1914_, lean_object* v_post_1915_, lean_object* v_usedLetOnly_1916_, lean_object* v_skipConstInApp_1917_, lean_object* v_skipInstances_1918_, lean_object* v_e_1919_, lean_object* v_a_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_usedLetOnly_boxed_1927_; uint8_t v_skipConstInApp_boxed_1928_; uint8_t v_skipInstances_boxed_1929_; lean_object* v_res_1930_; 
v_usedLetOnly_boxed_1927_ = lean_unbox(v_usedLetOnly_1916_);
v_skipConstInApp_boxed_1928_ = lean_unbox(v_skipConstInApp_1917_);
v_skipInstances_boxed_1929_ = lean_unbox(v_skipInstances_1918_);
v_res_1930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1914_, v_post_1915_, v_usedLetOnly_boxed_1927_, v_skipConstInApp_boxed_1928_, v_skipInstances_boxed_1929_, v_e_1919_, v_a_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v_a_1920_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1931_, lean_object* v_post_1932_, lean_object* v_usedLetOnly_1933_, lean_object* v_skipConstInApp_1934_, lean_object* v_skipInstances_1935_, lean_object* v_fvars_1936_, lean_object* v_e_1937_, lean_object* v_a_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v_usedLetOnly_boxed_1945_; uint8_t v_skipConstInApp_boxed_1946_; uint8_t v_skipInstances_boxed_1947_; lean_object* v_res_1948_; 
v_usedLetOnly_boxed_1945_ = lean_unbox(v_usedLetOnly_1933_);
v_skipConstInApp_boxed_1946_ = lean_unbox(v_skipConstInApp_1934_);
v_skipInstances_boxed_1947_ = lean_unbox(v_skipInstances_1935_);
v_res_1948_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1931_, v_post_1932_, v_usedLetOnly_boxed_1945_, v_skipConstInApp_boxed_1946_, v_skipInstances_boxed_1947_, v_fvars_1936_, v_e_1937_, v_a_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v_a_1938_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1949_, lean_object* v_post_1950_, lean_object* v_usedLetOnly_1951_, lean_object* v_skipConstInApp_1952_, lean_object* v_skipInstances_1953_, lean_object* v_fvars_1954_, lean_object* v_e_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_usedLetOnly_boxed_1963_; uint8_t v_skipConstInApp_boxed_1964_; uint8_t v_skipInstances_boxed_1965_; lean_object* v_res_1966_; 
v_usedLetOnly_boxed_1963_ = lean_unbox(v_usedLetOnly_1951_);
v_skipConstInApp_boxed_1964_ = lean_unbox(v_skipConstInApp_1952_);
v_skipInstances_boxed_1965_ = lean_unbox(v_skipInstances_1953_);
v_res_1966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1949_, v_post_1950_, v_usedLetOnly_boxed_1963_, v_skipConstInApp_boxed_1964_, v_skipInstances_boxed_1965_, v_fvars_1954_, v_e_1955_, v_a_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_a_1956_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1967_, lean_object* v_post_1968_, lean_object* v_usedLetOnly_1969_, lean_object* v_skipConstInApp_1970_, lean_object* v_skipInstances_1971_, lean_object* v_e_1972_, lean_object* v_a_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
uint8_t v_usedLetOnly_boxed_1980_; uint8_t v_skipConstInApp_boxed_1981_; uint8_t v_skipInstances_boxed_1982_; lean_object* v_res_1983_; 
v_usedLetOnly_boxed_1980_ = lean_unbox(v_usedLetOnly_1969_);
v_skipConstInApp_boxed_1981_ = lean_unbox(v_skipConstInApp_1970_);
v_skipInstances_boxed_1982_ = lean_unbox(v_skipInstances_1971_);
v_res_1983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1967_, v_post_1968_, v_usedLetOnly_boxed_1980_, v_skipConstInApp_boxed_1981_, v_skipInstances_boxed_1982_, v_e_1972_, v_a_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_a_1973_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1984_, lean_object* v_post_1985_, lean_object* v_usedLetOnly_1986_, lean_object* v_skipConstInApp_1987_, lean_object* v_skipInstances_1988_, lean_object* v_fvars_1989_, lean_object* v_e_1990_, lean_object* v_a_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v_usedLetOnly_boxed_1998_; uint8_t v_skipConstInApp_boxed_1999_; uint8_t v_skipInstances_boxed_2000_; lean_object* v_res_2001_; 
v_usedLetOnly_boxed_1998_ = lean_unbox(v_usedLetOnly_1986_);
v_skipConstInApp_boxed_1999_ = lean_unbox(v_skipConstInApp_1987_);
v_skipInstances_boxed_2000_ = lean_unbox(v_skipInstances_1988_);
v_res_2001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1984_, v_post_1985_, v_usedLetOnly_boxed_1998_, v_skipConstInApp_boxed_1999_, v_skipInstances_boxed_2000_, v_fvars_1989_, v_e_1990_, v_a_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v_a_1991_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2002_, lean_object* v___x_2003_, lean_object* v_pre_2004_, lean_object* v_post_2005_, lean_object* v_usedLetOnly_2006_, lean_object* v_skipConstInApp_2007_, lean_object* v_skipInstances_2008_, lean_object* v_a_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v_usedLetOnly_boxed_2018_; uint8_t v_skipConstInApp_boxed_2019_; uint8_t v_skipInstances_boxed_2020_; lean_object* v_res_2021_; 
v_usedLetOnly_boxed_2018_ = lean_unbox(v_usedLetOnly_2006_);
v_skipConstInApp_boxed_2019_ = lean_unbox(v_skipConstInApp_2007_);
v_skipInstances_boxed_2020_ = lean_unbox(v_skipInstances_2008_);
v_res_2021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2002_, v___x_2003_, v_pre_2004_, v_post_2005_, v_usedLetOnly_boxed_2018_, v_skipConstInApp_boxed_2019_, v_skipInstances_boxed_2020_, v_a_2009_, v_b_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2011_);
lean_dec_ref(v___x_2003_);
lean_dec(v_upperBound_2002_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2022_, lean_object* v_pre_2023_, lean_object* v_post_2024_, lean_object* v_usedLetOnly_2025_, lean_object* v_skipConstInApp_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v_skipInstances_boxed_2037_; uint8_t v_usedLetOnly_boxed_2038_; uint8_t v_skipConstInApp_boxed_2039_; lean_object* v_res_2040_; 
v_skipInstances_boxed_2037_ = lean_unbox(v_skipInstances_2022_);
v_usedLetOnly_boxed_2038_ = lean_unbox(v_usedLetOnly_2025_);
v_skipConstInApp_boxed_2039_ = lean_unbox(v_skipConstInApp_2026_);
v_res_2040_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2037_, v_pre_2023_, v_post_2024_, v_usedLetOnly_boxed_2038_, v_skipConstInApp_boxed_2039_, v_x_2027_, v_x_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2030_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_apply_1(v_x_2042_, lean_box(0));
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v___y_2043_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2052_, v_x_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_unsigned_to_nat(16u);
v___x_2063_ = lean_mk_array(v___x_2062_, v___x_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2068_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2068_, 0, lean_box(0));
lean_closure_set(v___x_2068_, 1, lean_box(0));
lean_closure_set(v___x_2068_, 2, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2069_, lean_object* v_pre_2070_, lean_object* v_post_2071_, uint8_t v_usedLetOnly_2072_, uint8_t v_skipConstInApp_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v_fst_2083_; lean_object* v_snd_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2080_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2081_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2080_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v_fst_2083_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_fst_2083_);
v_snd_2084_ = lean_ctor_get(v_a_2082_, 1);
lean_inc(v_snd_2084_);
lean_dec(v_a_2082_);
v___x_2085_ = 0;
v___x_2086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2070_, v_post_2071_, v_usedLetOnly_2072_, v_skipConstInApp_2073_, v___x_2085_, v_input_2069_, v_fst_2083_, v_snd_2084_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2108_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v_fst_2088_ = lean_ctor_get(v_a_2087_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_a_2087_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_a_2087_);
v___x_2090_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2090_, 0, lean_box(0));
lean_closure_set(v___x_2090_, 1, lean_box(0));
lean_closure_set(v___x_2090_, 2, v_fst_2083_);
v___x_2091_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2090_, v_snd_2089_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_snd_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2106_; 
v_snd_2096_ = lean_ctor_get(v_a_2092_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_a_2092_, 0);
lean_dec(v_unused_2107_);
v___x_2098_ = v_a_2092_;
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_snd_2096_);
lean_dec(v_a_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_fst_2088_);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fst_2088_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_snd_2096_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2101_);
v___x_2103_ = v___x_2094_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
else
{
lean_dec(v_fst_2083_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2109_, lean_object* v_pre_2110_, lean_object* v_post_2111_, lean_object* v_usedLetOnly_2112_, lean_object* v_skipConstInApp_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
uint8_t v_usedLetOnly_boxed_2120_; uint8_t v_skipConstInApp_boxed_2121_; lean_object* v_res_2122_; 
v_usedLetOnly_boxed_2120_ = lean_unbox(v_usedLetOnly_2112_);
v_skipConstInApp_boxed_2121_ = lean_unbox(v_skipConstInApp_2113_);
v_res_2122_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2109_, v_pre_2110_, v_post_2111_, v_usedLetOnly_boxed_2120_, v_skipConstInApp_boxed_2121_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2122_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2125_; uint64_t v___x_2126_; 
v___x_2125_ = 3;
v___x_2126_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; uint8_t v_foApprox_2134_; uint8_t v_ctxApprox_2135_; uint8_t v_quasiPatternApprox_2136_; uint8_t v_constApprox_2137_; uint8_t v_isDefEqStuckEx_2138_; uint8_t v_unificationHints_2139_; uint8_t v_proofIrrelevance_2140_; uint8_t v_assignSyntheticOpaque_2141_; uint8_t v_offsetCnstrs_2142_; uint8_t v_etaStruct_2143_; uint8_t v_univApprox_2144_; uint8_t v_iota_2145_; uint8_t v_beta_2146_; uint8_t v_proj_2147_; uint8_t v_zeta_2148_; uint8_t v_zetaDelta_2149_; uint8_t v_zetaUnused_2150_; uint8_t v_zetaHave_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2182_; 
v___x_2133_ = l_Lean_Meta_Context_config(v_a_2128_);
v_foApprox_2134_ = lean_ctor_get_uint8(v___x_2133_, 0);
v_ctxApprox_2135_ = lean_ctor_get_uint8(v___x_2133_, 1);
v_quasiPatternApprox_2136_ = lean_ctor_get_uint8(v___x_2133_, 2);
v_constApprox_2137_ = lean_ctor_get_uint8(v___x_2133_, 3);
v_isDefEqStuckEx_2138_ = lean_ctor_get_uint8(v___x_2133_, 4);
v_unificationHints_2139_ = lean_ctor_get_uint8(v___x_2133_, 5);
v_proofIrrelevance_2140_ = lean_ctor_get_uint8(v___x_2133_, 6);
v_assignSyntheticOpaque_2141_ = lean_ctor_get_uint8(v___x_2133_, 7);
v_offsetCnstrs_2142_ = lean_ctor_get_uint8(v___x_2133_, 8);
v_etaStruct_2143_ = lean_ctor_get_uint8(v___x_2133_, 10);
v_univApprox_2144_ = lean_ctor_get_uint8(v___x_2133_, 11);
v_iota_2145_ = lean_ctor_get_uint8(v___x_2133_, 12);
v_beta_2146_ = lean_ctor_get_uint8(v___x_2133_, 13);
v_proj_2147_ = lean_ctor_get_uint8(v___x_2133_, 14);
v_zeta_2148_ = lean_ctor_get_uint8(v___x_2133_, 15);
v_zetaDelta_2149_ = lean_ctor_get_uint8(v___x_2133_, 16);
v_zetaUnused_2150_ = lean_ctor_get_uint8(v___x_2133_, 17);
v_zetaHave_2151_ = lean_ctor_get_uint8(v___x_2133_, 18);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2153_ = v___x_2133_;
v_isShared_2154_ = v_isSharedCheck_2182_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2133_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2182_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
uint8_t v_trackZetaDelta_2155_; lean_object* v_zetaDeltaSet_2156_; lean_object* v_lctx_2157_; lean_object* v_localInstances_2158_; lean_object* v_defEqCtx_x3f_2159_; lean_object* v_synthPendingDepth_2160_; lean_object* v_canUnfold_x3f_2161_; uint8_t v_univApprox_2162_; uint8_t v_inTypeClassResolution_2163_; uint8_t v_cacheInferType_2164_; uint8_t v___x_2165_; lean_object* v_config_2167_; 
v_trackZetaDelta_2155_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*7);
v_zetaDeltaSet_2156_ = lean_ctor_get(v_a_2128_, 1);
v_lctx_2157_ = lean_ctor_get(v_a_2128_, 2);
v_localInstances_2158_ = lean_ctor_get(v_a_2128_, 3);
v_defEqCtx_x3f_2159_ = lean_ctor_get(v_a_2128_, 4);
v_synthPendingDepth_2160_ = lean_ctor_get(v_a_2128_, 5);
v_canUnfold_x3f_2161_ = lean_ctor_get(v_a_2128_, 6);
v_univApprox_2162_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2163_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*7 + 2);
v_cacheInferType_2164_ = lean_ctor_get_uint8(v_a_2128_, sizeof(void*)*7 + 3);
v___x_2165_ = 3;
if (v_isShared_2154_ == 0)
{
v_config_2167_ = v___x_2153_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 0, v_foApprox_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 1, v_ctxApprox_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 2, v_quasiPatternApprox_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 3, v_constApprox_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 4, v_isDefEqStuckEx_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 5, v_unificationHints_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 6, v_proofIrrelevance_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 7, v_assignSyntheticOpaque_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 8, v_offsetCnstrs_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 10, v_etaStruct_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 11, v_univApprox_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 12, v_iota_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 13, v_beta_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 14, v_proj_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 15, v_zeta_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 16, v_zetaDelta_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 17, v_zetaUnused_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, 18, v_zetaHave_2151_);
v_config_2167_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
uint64_t v___x_2168_; uint64_t v___x_2169_; uint64_t v___x_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v_key_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_ctor_set_uint8(v_config_2167_, 9, v___x_2165_);
v___x_2168_ = l_Lean_Meta_Context_configKey(v_a_2128_);
v___x_2169_ = 3ULL;
v___x_2170_ = lean_uint64_shift_right(v___x_2168_, v___x_2169_);
v___f_2171_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2172_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2173_ = 0;
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_uint64_shift_left(v___x_2170_, v___x_2169_);
v___x_2176_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2177_ = lean_uint64_lor(v___x_2175_, v___x_2176_);
v___x_2178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2178_, 0, v_config_2167_);
lean_ctor_set_uint64(v___x_2178_, sizeof(void*)*1, v_key_2177_);
lean_inc(v_canUnfold_x3f_2161_);
lean_inc(v_synthPendingDepth_2160_);
lean_inc(v_defEqCtx_x3f_2159_);
lean_inc_ref(v_localInstances_2158_);
lean_inc_ref(v_lctx_2157_);
lean_inc(v_zetaDeltaSet_2156_);
v___x_2179_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v_zetaDeltaSet_2156_);
lean_ctor_set(v___x_2179_, 2, v_lctx_2157_);
lean_ctor_set(v___x_2179_, 3, v_localInstances_2158_);
lean_ctor_set(v___x_2179_, 4, v_defEqCtx_x3f_2159_);
lean_ctor_set(v___x_2179_, 5, v_synthPendingDepth_2160_);
lean_ctor_set(v___x_2179_, 6, v_canUnfold_x3f_2161_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*7, v_trackZetaDelta_2155_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*7 + 1, v_univApprox_2162_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2163_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*7 + 3, v_cacheInferType_2164_);
v___x_2180_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2127_, v___f_2172_, v___f_2171_, v___x_2173_, v___x_2173_, v___x_2174_, v___x_2179_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec_ref_known(v___x_2179_, 7);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Meta_expandCoe(v_e_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2190_, lean_object* v_m_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2191_, v_a_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2194_, lean_object* v_m_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2194_, v_m_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_m_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2199_, v_x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
uint8_t v_res_2205_; lean_object* v_r_2206_; 
v_res_2205_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2202_, v_x_2203_, v_x_2204_);
lean_dec_ref(v_x_2204_);
lean_dec_ref(v_x_2203_);
v_r_2206_ = lean_box(v_res_2205_);
return v_r_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2207_, lean_object* v_a_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2208_, v_x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2211_, lean_object* v_a_2212_, lean_object* v_x_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2211_, v_a_2212_, v_x_2213_);
lean_dec(v_x_2213_);
lean_dec(v_a_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2215_, lean_object* v___x_2216_, lean_object* v_pre_2217_, lean_object* v_post_2218_, uint8_t v_usedLetOnly_2219_, uint8_t v_skipConstInApp_2220_, uint8_t v_skipInstances_2221_, lean_object* v___x_2222_, lean_object* v_inst_2223_, lean_object* v_R_2224_, lean_object* v_a_2225_, lean_object* v_b_2226_, lean_object* v_c_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2215_, v___x_2216_, v_pre_2217_, v_post_2218_, v_usedLetOnly_2219_, v_skipConstInApp_2220_, v_skipInstances_2221_, v_a_2225_, v_b_2226_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2236_ = _args[0];
lean_object* v___x_2237_ = _args[1];
lean_object* v_pre_2238_ = _args[2];
lean_object* v_post_2239_ = _args[3];
lean_object* v_usedLetOnly_2240_ = _args[4];
lean_object* v_skipConstInApp_2241_ = _args[5];
lean_object* v_skipInstances_2242_ = _args[6];
lean_object* v___x_2243_ = _args[7];
lean_object* v_inst_2244_ = _args[8];
lean_object* v_R_2245_ = _args[9];
lean_object* v_a_2246_ = _args[10];
lean_object* v_b_2247_ = _args[11];
lean_object* v_c_2248_ = _args[12];
lean_object* v___y_2249_ = _args[13];
lean_object* v___y_2250_ = _args[14];
lean_object* v___y_2251_ = _args[15];
lean_object* v___y_2252_ = _args[16];
lean_object* v___y_2253_ = _args[17];
lean_object* v___y_2254_ = _args[18];
lean_object* v___y_2255_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2256_; uint8_t v_skipConstInApp_boxed_2257_; uint8_t v_skipInstances_boxed_2258_; lean_object* v_res_2259_; 
v_usedLetOnly_boxed_2256_ = lean_unbox(v_usedLetOnly_2240_);
v_skipConstInApp_boxed_2257_ = lean_unbox(v_skipConstInApp_2241_);
v_skipInstances_boxed_2258_ = lean_unbox(v_skipInstances_2242_);
v_res_2259_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2236_, v___x_2237_, v_pre_2238_, v_post_2239_, v_usedLetOnly_boxed_2256_, v_skipConstInApp_boxed_2257_, v_skipInstances_boxed_2258_, v___x_2243_, v_inst_2244_, v_R_2245_, v_a_2246_, v_b_2247_, v_c_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2249_);
lean_dec(v___x_2243_);
lean_dec_ref(v___x_2237_);
lean_dec(v_upperBound_2236_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2260_, lean_object* v_m_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2261_, v_a_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2264_, lean_object* v_m_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2264_, v_m_2265_, v_a_2266_);
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_m_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2268_, lean_object* v_name_2269_, uint8_t v_bi_2270_, lean_object* v_type_2271_, lean_object* v_k_2272_, uint8_t v_kind_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2269_, v_bi_2270_, v_type_2271_, v_k_2272_, v_kind_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_name_2283_, lean_object* v_bi_2284_, lean_object* v_type_2285_, lean_object* v_k_2286_, lean_object* v_kind_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v_bi_boxed_2295_; uint8_t v_kind_boxed_2296_; lean_object* v_res_2297_; 
v_bi_boxed_2295_ = lean_unbox(v_bi_2284_);
v_kind_boxed_2296_ = lean_unbox(v_kind_2287_);
v_res_2297_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2282_, v_name_2283_, v_bi_boxed_2295_, v_type_2285_, v_k_2286_, v_kind_boxed_2296_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2288_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2298_, lean_object* v_name_2299_, lean_object* v_type_2300_, lean_object* v_val_2301_, lean_object* v_k_2302_, uint8_t v_nondep_2303_, uint8_t v_kind_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2299_, v_type_2300_, v_val_2301_, v_k_2302_, v_nondep_2303_, v_kind_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_name_2314_, lean_object* v_type_2315_, lean_object* v_val_2316_, lean_object* v_k_2317_, lean_object* v_nondep_2318_, lean_object* v_kind_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_nondep_boxed_2327_; uint8_t v_kind_boxed_2328_; lean_object* v_res_2329_; 
v_nondep_boxed_2327_ = lean_unbox(v_nondep_2318_);
v_kind_boxed_2328_ = lean_unbox(v_kind_2319_);
v_res_2329_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2313_, v_name_2314_, v_type_2315_, v_val_2316_, v_k_2317_, v_nondep_boxed_2327_, v_kind_boxed_2328_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2320_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2330_, lean_object* v_ref_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2331_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2338_, v_ref_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2346_, lean_object* v_x_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_x_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2356_, v_x_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2358_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2366_, lean_object* v_m_2367_, lean_object* v_a_2368_, lean_object* v_b_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2367_, v_a_2368_, v_b_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2371_, lean_object* v_x_2372_, size_t v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2372_, v_x_2373_, v_x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
size_t v_x_40474__boxed_2380_; uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_x_40474__boxed_2380_ = lean_unbox_usize(v_x_2378_);
lean_dec(v_x_2378_);
v_res_2381_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2376_, v_x_2377_, v_x_40474__boxed_2380_, v_x_2379_);
lean_dec_ref(v_x_2379_);
lean_dec_ref(v_x_2377_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2383_, lean_object* v_a_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2387_, lean_object* v_a_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2387_, v_a_2388_, v_x_2389_);
lean_dec(v_x_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2391_, lean_object* v_a_2392_, lean_object* v_x_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2392_, v_x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2395_, lean_object* v_a_2396_, lean_object* v_x_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2395_, v_a_2396_, v_x_2397_);
lean_dec(v_x_2397_);
lean_dec_ref(v_a_2396_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2400_, lean_object* v_data_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_, lean_object* v_x_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2404_, v_b_2405_, v_x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2408_, lean_object* v_keys_2409_, lean_object* v_vals_2410_, lean_object* v_heq_2411_, lean_object* v_i_2412_, lean_object* v_k_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2409_, v_i_2412_, v_k_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2415_, lean_object* v_keys_2416_, lean_object* v_vals_2417_, lean_object* v_heq_2418_, lean_object* v_i_2419_, lean_object* v_k_2420_){
_start:
{
uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_res_2421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2415_, v_keys_2416_, v_vals_2417_, v_heq_2418_, v_i_2419_, v_k_2420_);
lean_dec_ref(v_k_2420_);
lean_dec_ref(v_vals_2417_);
lean_dec_ref(v_keys_2416_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2423_, lean_object* v_i_2424_, lean_object* v_source_2425_, lean_object* v_target_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2424_, v_source_2425_, v_target_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2429_, v_x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2432_, lean_object* v_decl_2433_, lean_object* v_ref_2434_){
_start:
{
lean_object* v_defValue_2436_; lean_object* v_descr_2437_; lean_object* v_deprecation_x3f_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_defValue_2436_ = lean_ctor_get(v_decl_2433_, 0);
v_descr_2437_ = lean_ctor_get(v_decl_2433_, 1);
v_deprecation_x3f_2438_ = lean_ctor_get(v_decl_2433_, 2);
v___x_2439_ = lean_alloc_ctor(1, 0, 1);
v___x_2440_ = lean_unbox(v_defValue_2436_);
lean_ctor_set_uint8(v___x_2439_, 0, v___x_2440_);
lean_inc(v_deprecation_x3f_2438_);
lean_inc_ref(v_descr_2437_);
lean_inc_n(v_name_2432_, 2);
v___x_2441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2441_, 0, v_name_2432_);
lean_ctor_set(v___x_2441_, 1, v_ref_2434_);
lean_ctor_set(v___x_2441_, 2, v___x_2439_);
lean_ctor_set(v___x_2441_, 3, v_descr_2437_);
lean_ctor_set(v___x_2441_, 4, v_deprecation_x3f_2438_);
v___x_2442_ = lean_register_option(v_name_2432_, v___x_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2442_, 0);
lean_dec(v_unused_2451_);
v___x_2444_ = v___x_2442_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_dec(v___x_2442_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_inc(v_defValue_2436_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_name_2432_);
lean_ctor_set(v___x_2446_, 1, v_defValue_2436_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_name_2432_);
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2460_, lean_object* v_decl_2461_, lean_object* v_ref_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2460_, v_decl_2461_, v_ref_2462_);
lean_dec_ref(v_decl_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2481_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2482_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2479_, v___x_2480_, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_ref_2491_; lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2501_; 
v_ref_2491_ = lean_ctor_get(v___y_2488_, 5);
v___x_2492_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_inc(v_ref_2491_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_ref_2491_);
lean_ctor_set(v___x_2497_, 1, v_a_2493_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2497_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2524_, lean_object* v_expectedType_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; 
lean_inc(v_a_2529_);
lean_inc_ref(v_a_2528_);
lean_inc(v_a_2527_);
lean_inc_ref(v_a_2526_);
lean_inc_ref(v_expr_2524_);
v___x_2531_ = lean_infer_type(v_expr_2524_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_n(v_a_2532_, 2);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_Meta_getLevel(v_a_2532_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
lean_inc_ref(v_expectedType_2525_);
v___x_2535_ = l_Lean_Meta_getLevel(v_expectedType_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_a_2536_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2534_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
lean_inc_ref(v___x_2540_);
v___x_2541_ = l_Lean_mkConst(v___x_2537_, v___x_2540_);
v___x_2542_ = lean_unsigned_to_nat(3u);
v___x_2543_ = lean_mk_empty_array_with_capacity(v___x_2542_);
lean_inc(v_a_2532_);
v___x_2544_ = lean_array_push(v___x_2543_, v_a_2532_);
lean_inc_ref(v_expr_2524_);
v___x_2545_ = lean_array_push(v___x_2544_, v_expr_2524_);
lean_inc_ref(v_expectedType_2525_);
v___x_2546_ = lean_array_push(v___x_2545_, v_expectedType_2525_);
v___x_2547_ = l_Lean_mkAppN(v___x_2541_, v___x_2546_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = lean_box(0);
v___x_2549_ = l_Lean_Meta_trySynthInstance(v___x_2547_, v___x_2548_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2647_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2647_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2647_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
switch(lean_obj_tag(v_a_2550_))
{
case 0:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec_ref_known(v___x_2540_, 2);
lean_dec(v_a_2532_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v___x_2554_ = lean_box(0);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
case 1:
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2642_; 
lean_del_object(v___x_2552_);
v_a_2558_ = lean_ctor_get(v_a_2550_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2550_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2560_ = v_a_2550_;
v_isShared_2561_ = v_isSharedCheck_2642_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v_a_2550_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2642_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2562_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2563_ = l_Lean_mkConst(v___x_2562_, v___x_2540_);
v___x_2564_ = lean_unsigned_to_nat(4u);
v___x_2565_ = lean_mk_empty_array_with_capacity(v___x_2564_);
v___x_2566_ = lean_array_push(v___x_2565_, v_a_2532_);
lean_inc_ref(v_expr_2524_);
v___x_2567_ = lean_array_push(v___x_2566_, v_expr_2524_);
lean_inc_ref(v_expectedType_2525_);
v___x_2568_ = lean_array_push(v___x_2567_, v_expectedType_2525_);
v___x_2569_ = lean_array_push(v___x_2568_, v_a_2558_);
v___x_2570_ = l_Lean_mkAppN(v___x_2563_, v___x_2569_);
lean_dec_ref(v___x_2569_);
v___x_2571_ = l_Lean_Meta_expandCoe(v___x_2570_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2633_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2633_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2633_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_fst_2583_; lean_object* v___x_2584_; 
v_fst_2583_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_a_2529_);
lean_inc_ref(v_a_2528_);
lean_inc(v_a_2527_);
lean_inc_ref(v_a_2526_);
lean_inc(v_fst_2583_);
v___x_2584_ = lean_infer_type(v_fst_2583_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
lean_inc_ref(v_expectedType_2525_);
v___x_2586_ = l_Lean_Meta_isExprDefEq(v_a_2585_, v_expectedType_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; uint8_t v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = lean_unbox(v_a_2587_);
lean_dec(v_a_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2614_; 
lean_inc(v_fst_2583_);
lean_del_object(v___x_2574_);
lean_del_object(v___x_2560_);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_a_2572_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; lean_object* v_unused_2616_; 
v_unused_2615_ = lean_ctor_get(v_a_2572_, 1);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_a_2572_, 0);
lean_dec(v_unused_2616_);
v___x_2590_ = v_a_2572_;
v_isShared_2591_ = v_isSharedCheck_2614_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v_a_2572_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2614_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2592_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2593_ = l_Lean_indentExpr(v_expr_2524_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 7);
lean_ctor_set(v___x_2590_, 1, v___x_2593_);
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v___x_2596_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_indentExpr(v_expectedType_2525_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = l_Lean_indentExpr(v_fst_2583_);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2603_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_del_object(v___x_2574_);
lean_dec(v_a_2572_);
lean_del_object(v___x_2560_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2617_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2586_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2586_);
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
lean_del_object(v___x_2574_);
lean_dec(v_a_2572_);
lean_del_object(v___x_2560_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2625_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2584_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2584_);
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
v___jp_2576_:
{
lean_object* v___x_2578_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_a_2572_);
v___x_2578_ = v___x_2560_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2572_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2578_);
v___x_2580_ = v___x_2574_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_del_object(v___x_2560_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2634_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2571_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2571_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
default: 
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_dec_ref_known(v___x_2540_, 2);
lean_dec(v_a_2532_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v___x_2643_ = lean_box(2);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2643_);
v___x_2645_ = v___x_2552_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref_known(v___x_2540_, 2);
lean_dec(v_a_2532_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2648_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2549_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2549_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_a_2534_);
lean_dec(v_a_2532_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2656_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2535_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2535_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_a_2532_);
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2664_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2533_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2533_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_expectedType_2525_);
lean_dec_ref(v_expr_2524_);
v_a_2672_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2531_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2531_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2680_, lean_object* v_expectedType_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2680_, v_expectedType_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2688_, lean_object* v_msg_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2696_, v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2704_, lean_object* v_expectedType_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2704_, v_expectedType_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2736_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2736_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2736_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
switch(lean_obj_tag(v_a_2712_))
{
case 0:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_box(0);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
case 1:
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2731_; 
v_a_2720_ = lean_ctor_get(v_a_2712_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_a_2712_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2722_ = v_a_2712_;
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v_a_2712_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_fst_2724_; lean_object* v___x_2726_; 
v_fst_2724_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_fst_2724_);
lean_dec(v_a_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v_fst_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_fst_2724_);
v___x_2726_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2726_);
v___x_2728_ = v___x_2714_;
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
default: 
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_box(2);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2732_);
v___x_2734_ = v___x_2714_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
v_a_2737_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2711_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2711_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2745_, lean_object* v_expectedType_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2745_, v_expectedType_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2752_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2761_ = l_Lean_stringToMessageData(v___x_2760_);
return v___x_2761_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2767_ = l_Lean_stringToMessageData(v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v___x_2774_; 
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
lean_inc_ref(v_expr_2768_);
v___x_2774_ = lean_infer_type(v_expr_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_n(v_a_2775_, 2);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = l_Lean_Meta_getLevel(v_a_2775_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_n(v_a_2779_, 2);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_mkSort(v_a_2779_);
lean_inc(v_a_2775_);
v___x_2781_ = l_Lean_mkArrow(v_a_2775_, v___x_2780_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_a_2782_);
v___x_2784_ = 0;
v___x_2785_ = lean_box(0);
v___x_2786_ = l_Lean_Meta_mkFreshExprMVar(v___x_2783_, v___x_2784_, v___x_2785_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc_n(v_a_2787_, 2);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_a_2779_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2777_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_inc_ref(v___x_2791_);
v___x_2792_ = l_Lean_Expr_const___override(v___x_2788_, v___x_2791_);
lean_inc(v_a_2775_);
v___x_2793_ = l_Lean_mkAppB(v___x_2792_, v_a_2775_, v_a_2787_);
v___x_2794_ = lean_box(0);
v___x_2795_ = l_Lean_Meta_trySynthInstance(v___x_2793_, v___x_2794_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2882_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2882_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2882_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_a_2796_) == 1)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2878_; 
lean_del_object(v___x_2798_);
v_a_2800_ = lean_ctor_get(v_a_2796_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2802_ = v_a_2796_;
v_isShared_2803_ = v_isSharedCheck_2878_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v_a_2796_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2878_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2804_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2805_ = l_Lean_Expr_const___override(v___x_2804_, v___x_2791_);
lean_inc_ref(v_expr_2768_);
lean_inc(v_a_2800_);
v___x_2806_ = l_Lean_mkApp4(v___x_2805_, v_a_2775_, v_a_2787_, v_a_2800_, v_expr_2768_);
v___x_2807_ = l_Lean_Meta_expandCoe(v___x_2806_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2869_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2869_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2869_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v_fst_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2867_; 
v_fst_2812_ = lean_ctor_get(v_a_2808_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_a_2808_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v_a_2808_, 1);
lean_dec(v_unused_2868_);
v___x_2814_ = v_a_2808_;
v_isShared_2815_ = v_isSharedCheck_2867_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_fst_2812_);
lean_dec(v_a_2808_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2867_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2823_; 
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
lean_inc(v_fst_2812_);
v___x_2823_ = lean_infer_type(v_fst_2812_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
v___x_2825_ = lean_whnf(v_a_2824_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; uint8_t v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l_Lean_Expr_isForall(v_a_2826_);
lean_dec(v_a_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_del_object(v___x_2810_);
lean_del_object(v___x_2802_);
v___x_2828_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2829_ = l_Lean_indentExpr(v_expr_2768_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 7);
lean_ctor_set(v___x_2814_, 1, v___x_2829_);
lean_ctor_set(v___x_2814_, 0, v___x_2828_);
v___x_2831_ = v___x_2814_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v___x_2832_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Lean_indentExpr(v_fst_2812_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2837_ = l_Lean_indentExpr(v_a_2800_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_MessageData_hint_x27(v___x_2838_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2835_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2840_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
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
else
{
lean_del_object(v___x_2814_);
lean_dec(v_a_2800_);
lean_dec_ref(v_expr_2768_);
goto v___jp_2816_;
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2814_);
lean_dec(v_fst_2812_);
lean_del_object(v___x_2810_);
lean_del_object(v___x_2802_);
lean_dec(v_a_2800_);
lean_dec_ref(v_expr_2768_);
v_a_2851_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2825_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2825_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_del_object(v___x_2814_);
lean_dec(v_fst_2812_);
lean_del_object(v___x_2810_);
lean_del_object(v___x_2802_);
lean_dec(v_a_2800_);
lean_dec_ref(v_expr_2768_);
v_a_2859_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2823_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2823_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
v___jp_2816_:
{
lean_object* v___x_2818_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_fst_2812_);
v___x_2818_ = v___x_2802_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_fst_2812_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2818_);
v___x_2820_ = v___x_2810_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_del_object(v___x_2802_);
lean_dec(v_a_2800_);
lean_dec_ref(v_expr_2768_);
v_a_2870_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2807_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2807_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
lean_object* v___x_2880_; 
lean_dec(v_a_2796_);
lean_dec_ref_known(v___x_2791_, 2);
lean_dec(v_a_2787_);
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2794_);
v___x_2880_ = v___x_2798_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2794_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref_known(v___x_2791_, 2);
lean_dec(v_a_2787_);
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
v_a_2883_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2795_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2795_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_a_2779_);
lean_dec(v_a_2777_);
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
v_a_2891_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2786_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2786_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2779_);
lean_dec(v_a_2777_);
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
v_a_2899_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2781_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2781_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_a_2777_);
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
v_a_2907_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2778_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2778_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2775_);
lean_dec_ref(v_expr_2768_);
v_a_2915_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2776_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2776_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref(v_expr_2768_);
v_a_2923_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2774_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2774_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2937_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2949_ = l_Lean_stringToMessageData(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___x_2956_; 
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
lean_inc_ref(v_expr_2950_);
v___x_2956_ = lean_infer_type(v_expr_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_n(v_a_2957_, 2);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l_Lean_Meta_getLevel(v_a_2957_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc_n(v_a_2961_, 2);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l_Lean_mkSort(v_a_2961_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
v___x_2964_ = 0;
v___x_2965_ = lean_box(0);
v___x_2966_ = l_Lean_Meta_mkFreshExprMVar(v___x_2963_, v___x_2964_, v___x_2965_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_n(v_a_2967_, 2);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_a_2961_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_a_2959_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
lean_inc_ref(v___x_2971_);
v___x_2972_ = l_Lean_Expr_const___override(v___x_2968_, v___x_2971_);
lean_inc(v_a_2957_);
v___x_2973_ = l_Lean_mkAppB(v___x_2972_, v_a_2957_, v_a_2967_);
v___x_2974_ = lean_box(0);
v___x_2975_ = l_Lean_Meta_trySynthInstance(v___x_2973_, v___x_2974_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3062_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3062_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3062_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
if (lean_obj_tag(v_a_2976_) == 1)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3058_; 
lean_del_object(v___x_2978_);
v_a_2980_ = lean_ctor_get(v_a_2976_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_2982_ = v_a_2976_;
v_isShared_2983_ = v_isSharedCheck_3058_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v_a_2976_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3058_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2984_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2985_ = l_Lean_Expr_const___override(v___x_2984_, v___x_2971_);
lean_inc_ref(v_expr_2950_);
lean_inc(v_a_2980_);
v___x_2986_ = l_Lean_mkApp4(v___x_2985_, v_a_2957_, v_a_2967_, v_a_2980_, v_expr_2950_);
v___x_2987_ = l_Lean_Meta_expandCoe(v___x_2986_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3049_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_3049_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3049_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_fst_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3047_; 
v_fst_2992_ = lean_ctor_get(v_a_2988_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_a_2988_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v_a_2988_, 1);
lean_dec(v_unused_3048_);
v___x_2994_ = v_a_2988_;
v_isShared_2995_ = v_isSharedCheck_3047_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_fst_2992_);
lean_dec(v_a_2988_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3047_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_3003_; 
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
lean_inc(v_fst_2992_);
v___x_3003_ = lean_infer_type(v_fst_2992_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
lean_inc(v_a_2954_);
lean_inc_ref(v_a_2953_);
lean_inc(v_a_2952_);
lean_inc_ref(v_a_2951_);
v___x_3005_ = lean_whnf(v_a_3004_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; uint8_t v___x_3007_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_Expr_isSort(v_a_3006_);
lean_dec(v_a_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_del_object(v___x_2990_);
lean_del_object(v___x_2982_);
v___x_3008_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3009_ = l_Lean_indentExpr(v_expr_2950_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 7);
lean_ctor_set(v___x_2994_, 1, v___x_3009_);
lean_ctor_set(v___x_2994_, 0, v___x_3008_);
v___x_3011_ = v___x_2994_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v___x_3012_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = l_Lean_indentExpr(v_fst_2992_);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3017_ = l_Lean_indentExpr(v_a_2980_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_MessageData_hint_x27(v___x_3018_);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3015_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3020_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
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
else
{
lean_del_object(v___x_2994_);
lean_dec(v_a_2980_);
lean_dec_ref(v_expr_2950_);
goto v___jp_2996_;
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2980_);
lean_dec_ref(v_expr_2950_);
v_a_3031_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3005_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3005_);
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
lean_del_object(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
lean_del_object(v___x_2982_);
lean_dec(v_a_2980_);
lean_dec_ref(v_expr_2950_);
v_a_3039_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3003_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3003_);
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
v___jp_2996_:
{
lean_object* v___x_2998_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_fst_2992_);
v___x_2998_ = v___x_2982_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_fst_2992_);
v___x_2998_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2998_);
v___x_3000_ = v___x_2990_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_2982_);
lean_dec(v_a_2980_);
lean_dec_ref(v_expr_2950_);
v_a_3050_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2987_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2987_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v___x_3060_; 
lean_dec(v_a_2976_);
lean_dec_ref_known(v___x_2971_, 2);
lean_dec(v_a_2967_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2950_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2974_);
v___x_3060_ = v___x_2978_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_2974_);
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
lean_dec_ref_known(v___x_2971_, 2);
lean_dec(v_a_2967_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2950_);
v_a_3063_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2975_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2975_);
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
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2950_);
v_a_3071_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2966_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2966_);
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
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2950_);
v_a_3079_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2960_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2960_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_a_2957_);
lean_dec_ref(v_expr_2950_);
v_a_3087_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2958_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2958_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_expr_2950_);
v_a_3095_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_2956_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_2956_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3110_, lean_object* v___y_3111_){
_start:
{
uint8_t v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = l_Lean_Expr_hasMVar(v_e_3110_);
v___x_3114_ = lean_bool_not(v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v_mctx_3116_; lean_object* v___x_3117_; lean_object* v_fst_3118_; lean_object* v_snd_3119_; lean_object* v___x_3120_; lean_object* v_cache_3121_; lean_object* v_zetaDeltaFVarIds_3122_; lean_object* v_postponed_3123_; lean_object* v_diag_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3133_; 
v___x_3115_ = lean_st_ref_get(v___y_3111_);
v_mctx_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc_ref(v_mctx_3116_);
lean_dec(v___x_3115_);
v___x_3117_ = l_Lean_instantiateMVarsCore(v_mctx_3116_, v_e_3110_);
v_fst_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_fst_3118_);
v_snd_3119_ = lean_ctor_get(v___x_3117_, 1);
lean_inc(v_snd_3119_);
lean_dec_ref(v___x_3117_);
v___x_3120_ = lean_st_ref_take(v___y_3111_);
v_cache_3121_ = lean_ctor_get(v___x_3120_, 1);
v_zetaDeltaFVarIds_3122_ = lean_ctor_get(v___x_3120_, 2);
v_postponed_3123_ = lean_ctor_get(v___x_3120_, 3);
v_diag_3124_ = lean_ctor_get(v___x_3120_, 4);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_3120_, 0);
lean_dec(v_unused_3134_);
v___x_3126_ = v___x_3120_;
v_isShared_3127_ = v_isSharedCheck_3133_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_diag_3124_);
lean_inc(v_postponed_3123_);
lean_inc(v_zetaDeltaFVarIds_3122_);
lean_inc(v_cache_3121_);
lean_dec(v___x_3120_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3133_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v_snd_3119_);
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_snd_3119_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_cache_3121_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_zetaDeltaFVarIds_3122_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_postponed_3123_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_diag_3124_);
v___x_3129_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_st_ref_set(v___y_3111_, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_fst_3118_);
return v___x_3131_;
}
}
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_e_3110_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3136_, v___y_3137_);
lean_dec(v___y_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3140_, v___y_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3153_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3154_; uint64_t v___x_3155_; 
v___x_3154_ = 2;
v___x_3155_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___x_3162_; uint8_t v_foApprox_3163_; uint8_t v_ctxApprox_3164_; uint8_t v_quasiPatternApprox_3165_; uint8_t v_constApprox_3166_; uint8_t v_isDefEqStuckEx_3167_; uint8_t v_unificationHints_3168_; uint8_t v_proofIrrelevance_3169_; uint8_t v_assignSyntheticOpaque_3170_; uint8_t v_offsetCnstrs_3171_; uint8_t v_etaStruct_3172_; uint8_t v_univApprox_3173_; uint8_t v_iota_3174_; uint8_t v_beta_3175_; uint8_t v_proj_3176_; uint8_t v_zeta_3177_; uint8_t v_zetaDelta_3178_; uint8_t v_zetaUnused_3179_; uint8_t v_zetaHave_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3245_; 
v___x_3162_ = l_Lean_Meta_Context_config(v_a_3157_);
v_foApprox_3163_ = lean_ctor_get_uint8(v___x_3162_, 0);
v_ctxApprox_3164_ = lean_ctor_get_uint8(v___x_3162_, 1);
v_quasiPatternApprox_3165_ = lean_ctor_get_uint8(v___x_3162_, 2);
v_constApprox_3166_ = lean_ctor_get_uint8(v___x_3162_, 3);
v_isDefEqStuckEx_3167_ = lean_ctor_get_uint8(v___x_3162_, 4);
v_unificationHints_3168_ = lean_ctor_get_uint8(v___x_3162_, 5);
v_proofIrrelevance_3169_ = lean_ctor_get_uint8(v___x_3162_, 6);
v_assignSyntheticOpaque_3170_ = lean_ctor_get_uint8(v___x_3162_, 7);
v_offsetCnstrs_3171_ = lean_ctor_get_uint8(v___x_3162_, 8);
v_etaStruct_3172_ = lean_ctor_get_uint8(v___x_3162_, 10);
v_univApprox_3173_ = lean_ctor_get_uint8(v___x_3162_, 11);
v_iota_3174_ = lean_ctor_get_uint8(v___x_3162_, 12);
v_beta_3175_ = lean_ctor_get_uint8(v___x_3162_, 13);
v_proj_3176_ = lean_ctor_get_uint8(v___x_3162_, 14);
v_zeta_3177_ = lean_ctor_get_uint8(v___x_3162_, 15);
v_zetaDelta_3178_ = lean_ctor_get_uint8(v___x_3162_, 16);
v_zetaUnused_3179_ = lean_ctor_get_uint8(v___x_3162_, 17);
v_zetaHave_3180_ = lean_ctor_get_uint8(v___x_3162_, 18);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3182_ = v___x_3162_;
v_isShared_3183_ = v_isSharedCheck_3245_;
goto v_resetjp_3181_;
}
else
{
lean_dec(v___x_3162_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3245_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
uint8_t v_trackZetaDelta_3184_; lean_object* v_zetaDeltaSet_3185_; lean_object* v_lctx_3186_; lean_object* v_localInstances_3187_; lean_object* v_defEqCtx_x3f_3188_; lean_object* v_synthPendingDepth_3189_; lean_object* v_canUnfold_x3f_3190_; uint8_t v_univApprox_3191_; uint8_t v_inTypeClassResolution_3192_; uint8_t v_cacheInferType_3193_; uint8_t v___x_3194_; lean_object* v_config_3196_; 
v_trackZetaDelta_3184_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7);
v_zetaDeltaSet_3185_ = lean_ctor_get(v_a_3157_, 1);
v_lctx_3186_ = lean_ctor_get(v_a_3157_, 2);
v_localInstances_3187_ = lean_ctor_get(v_a_3157_, 3);
v_defEqCtx_x3f_3188_ = lean_ctor_get(v_a_3157_, 4);
v_synthPendingDepth_3189_ = lean_ctor_get(v_a_3157_, 5);
v_canUnfold_x3f_3190_ = lean_ctor_get(v_a_3157_, 6);
v_univApprox_3191_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3192_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 2);
v_cacheInferType_3193_ = lean_ctor_get_uint8(v_a_3157_, sizeof(void*)*7 + 3);
v___x_3194_ = 2;
if (v_isShared_3183_ == 0)
{
v_config_3196_ = v___x_3182_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 0, v_foApprox_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 1, v_ctxApprox_3164_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 2, v_quasiPatternApprox_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 3, v_constApprox_3166_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 4, v_isDefEqStuckEx_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 5, v_unificationHints_3168_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 6, v_proofIrrelevance_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 7, v_assignSyntheticOpaque_3170_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 8, v_offsetCnstrs_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 10, v_etaStruct_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 11, v_univApprox_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 12, v_iota_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 13, v_beta_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 14, v_proj_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 15, v_zeta_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 16, v_zetaDelta_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 17, v_zetaUnused_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3244_, 18, v_zetaHave_3180_);
v_config_3196_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
uint64_t v___x_3197_; uint64_t v___x_3198_; uint64_t v___x_3199_; uint64_t v___x_3200_; uint64_t v___x_3201_; uint64_t v_key_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_ctor_set_uint8(v_config_3196_, 9, v___x_3194_);
v___x_3197_ = l_Lean_Meta_Context_configKey(v_a_3157_);
v___x_3198_ = 3ULL;
v___x_3199_ = lean_uint64_shift_right(v___x_3197_, v___x_3198_);
v___x_3200_ = lean_uint64_shift_left(v___x_3199_, v___x_3198_);
v___x_3201_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3202_ = lean_uint64_lor(v___x_3200_, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3203_, 0, v_config_3196_);
lean_ctor_set_uint64(v___x_3203_, sizeof(void*)*1, v_key_3202_);
lean_inc(v_canUnfold_x3f_3190_);
lean_inc(v_synthPendingDepth_3189_);
lean_inc(v_defEqCtx_x3f_3188_);
lean_inc_ref(v_localInstances_3187_);
lean_inc_ref(v_lctx_3186_);
lean_inc(v_zetaDeltaSet_3185_);
v___x_3204_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v_zetaDeltaSet_3185_);
lean_ctor_set(v___x_3204_, 2, v_lctx_3186_);
lean_ctor_set(v___x_3204_, 3, v_localInstances_3187_);
lean_ctor_set(v___x_3204_, 4, v_defEqCtx_x3f_3188_);
lean_ctor_set(v___x_3204_, 5, v_synthPendingDepth_3189_);
lean_ctor_set(v___x_3204_, 6, v_canUnfold_x3f_3190_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*7, v_trackZetaDelta_3184_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*7 + 1, v_univApprox_3191_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3192_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*7 + 3, v_cacheInferType_3193_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
v___x_3205_ = lean_whnf(v_type_3156_, v___x_3204_, v_a_3158_, v_a_3159_, v_a_3160_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3235_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3235_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3235_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
if (lean_obj_tag(v_a_3206_) == 5)
{
lean_object* v_fn_3210_; lean_object* v_arg_3211_; lean_object* v___x_3212_; lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3230_; 
lean_del_object(v___x_3208_);
v_fn_3210_ = lean_ctor_get(v_a_3206_, 0);
lean_inc_ref(v_fn_3210_);
v_arg_3211_ = lean_ctor_get(v_a_3206_, 1);
lean_inc_ref(v_arg_3211_);
lean_dec_ref_known(v_a_3206_, 2);
v___x_3212_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3210_, v_a_3158_);
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3230_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3230_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3229_; 
v___x_3217_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3211_, v_a_3158_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3229_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3229_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v_a_3213_);
lean_ctor_set(v___x_3222_, 1, v_a_3218_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 1);
lean_ctor_set(v___x_3215_, 0, v___x_3222_);
v___x_3224_ = v___x_3215_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3224_);
v___x_3226_ = v___x_3220_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_dec(v_a_3206_);
v___x_3231_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3231_);
v___x_3233_ = v___x_3208_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
v_a_3236_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3205_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3205_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_Meta_isTypeApp_x3f(v_type_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Meta_isTypeApp_x3f(v_type_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3295_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3295_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3295_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
if (lean_obj_tag(v_a_3260_) == 1)
{
lean_object* v_val_3264_; lean_object* v_fst_3265_; lean_object* v___x_3266_; 
lean_del_object(v___x_3262_);
v_val_3264_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v_a_3260_, 1);
v_fst_3265_ = lean_ctor_get(v_val_3264_, 0);
lean_inc(v_fst_3265_);
lean_dec(v_val_3264_);
v___x_3266_ = l_Lean_Meta_isMonad_x3f(v_fst_3265_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3281_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3281_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3281_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
if (lean_obj_tag(v_a_3267_) == 0)
{
uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3271_ = 0;
v___x_3272_ = lean_box(v___x_3271_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3272_);
v___x_3274_ = v___x_3269_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
else
{
uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_dec_ref_known(v_a_3267_, 1);
v___x_3276_ = 1;
v___x_3277_ = lean_box(v___x_3276_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3277_);
v___x_3279_ = v___x_3269_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v_a_3282_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3266_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3266_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
uint8_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
lean_dec(v_a_3260_);
v___x_3290_ = 0;
v___x_3291_ = lean_box(v___x_3290_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3291_);
v___x_3293_ = v___x_3262_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3259_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3259_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Meta_isMonadApp(v_type_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
return v_res_3310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3311_, lean_object* v_opt_3312_){
_start:
{
lean_object* v_name_3313_; lean_object* v_defValue_3314_; lean_object* v_map_3315_; lean_object* v___x_3316_; 
v_name_3313_ = lean_ctor_get(v_opt_3312_, 0);
v_defValue_3314_ = lean_ctor_get(v_opt_3312_, 1);
v_map_3315_ = lean_ctor_get(v_opts_3311_, 0);
v___x_3316_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3315_, v_name_3313_);
if (lean_obj_tag(v___x_3316_) == 0)
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_unbox(v_defValue_3314_);
return v___x_3317_;
}
else
{
lean_object* v_val_3318_; 
v_val_3318_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v___x_3316_, 1);
if (lean_obj_tag(v_val_3318_) == 1)
{
uint8_t v_v_3319_; 
v_v_3319_ = lean_ctor_get_uint8(v_val_3318_, 0);
lean_dec_ref_known(v_val_3318_, 0);
return v_v_3319_;
}
else
{
uint8_t v___x_3320_; 
lean_dec(v_val_3318_);
v___x_3320_ = lean_unbox(v_defValue_3314_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3321_, lean_object* v_opt_3322_){
_start:
{
uint8_t v_res_3323_; lean_object* v_r_3324_; 
v_res_3323_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3321_, v_opt_3322_);
lean_dec_ref(v_opt_3322_);
lean_dec_ref(v_opts_3321_);
v_r_3324_ = lean_box(v_res_3323_);
return v_r_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v_x_3335_);
return v_res_3341_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = l_Lean_mkBVar(v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3364_, lean_object* v_expectedType_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v_a_3378_; lean_object* v___y_3382_; lean_object* v___x_3392_; lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3796_; 
v___x_3392_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3365_, v_a_3367_);
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3796_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3796_;
goto v_resetjp_3394_;
}
v___jp_3371_:
{
if (v___y_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___y_3372_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___y_3372_);
return v___x_3376_;
}
}
v___jp_3377_:
{
uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_Exception_isInterrupt(v_a_3378_);
if (v___x_3379_ == 0)
{
uint8_t v___x_3380_; 
lean_inc_ref(v_a_3378_);
v___x_3380_ = l_Lean_Exception_isRuntime(v_a_3378_);
v___y_3372_ = v_a_3378_;
v___y_3373_ = v___x_3380_;
goto v___jp_3371_;
}
else
{
v___y_3372_ = v_a_3378_;
v___y_3373_ = v___x_3379_;
goto v___jp_3371_;
}
}
v___jp_3381_:
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3391_; 
v_a_3383_ = lean_ctor_get(v___y_3382_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___y_3382_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3385_ = v___y_3382_;
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___y_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_a_3387_; lean_object* v___x_3389_; 
v_a_3387_ = lean_ctor_get(v_a_3383_, 0);
lean_inc(v_a_3387_);
lean_dec(v_a_3383_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v_a_3387_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; 
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc_ref(v_e_3364_);
v___x_3397_ = lean_infer_type(v_e_3364_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3787_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v___x_3399_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3398_, v_a_3367_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3787_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3787_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; 
lean_inc(v_a_3393_);
v___x_3404_ = l_Lean_Meta_isTypeApp_x3f(v_a_3393_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3778_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3778_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3778_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
if (lean_obj_tag(v_a_3405_) == 1)
{
lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3407_);
v_val_3409_ = lean_ctor_get(v_a_3405_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3773_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3773_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3772_; 
v_fst_3413_ = lean_ctor_get(v_val_3409_, 0);
v_snd_3414_ = lean_ctor_get(v_val_3409_, 1);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_val_3409_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3416_ = v_val_3409_;
v_isShared_3417_ = v_isSharedCheck_3772_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_snd_3414_);
lean_inc(v_fst_3413_);
lean_dec(v_val_3409_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3772_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; 
lean_inc(v_a_3400_);
v___x_3418_ = l_Lean_Meta_isTypeApp_x3f(v_a_3400_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3763_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3763_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3763_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
if (lean_obj_tag(v_a_3419_) == 1)
{
lean_object* v_val_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3758_; 
lean_del_object(v___x_3421_);
v_val_3423_ = lean_ctor_get(v_a_3419_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3425_ = v_a_3419_;
v_isShared_3426_ = v_isSharedCheck_3758_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_val_3423_);
lean_dec(v_a_3419_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3758_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3757_; 
v_fst_3427_ = lean_ctor_get(v_val_3423_, 0);
v_snd_3428_ = lean_ctor_get(v_val_3423_, 1);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_val_3423_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3430_ = v_val_3423_;
v_isShared_3431_ = v_isSharedCheck_3757_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_inc(v_fst_3427_);
lean_dec(v_val_3423_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3757_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_Meta_saveState___redArg(v_a_3367_, v_a_3369_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
lean_inc(v_fst_3413_);
lean_inc(v_fst_3427_);
v___x_3434_ = l_Lean_Meta_isExprDefEq(v_fst_3427_, v_fst_3413_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3740_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3740_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3740_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3439_ == 0)
{
lean_object* v_options_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
lean_dec(v_a_3433_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_del_object(v___x_3395_);
v_options_3440_ = lean_ctor_get(v_a_3368_, 2);
v___x_3441_ = l_Lean_Meta_autoLift;
v___x_3442_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3443_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3443_);
v___x_3445_ = v___x_3437_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
else
{
lean_object* v___x_3447_; 
lean_del_object(v___x_3437_);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc(v_fst_3427_);
v___x_3447_ = lean_infer_type(v_fst_3427_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
v___x_3449_ = lean_whnf(v_a_3448_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
if (lean_obj_tag(v_a_3450_) == 7)
{
lean_object* v_binderType_3451_; 
v_binderType_3451_ = lean_ctor_get(v_a_3450_, 1);
if (lean_obj_tag(v_binderType_3451_) == 3)
{
lean_object* v_body_3452_; 
v_body_3452_ = lean_ctor_get(v_a_3450_, 2);
if (lean_obj_tag(v_body_3452_) == 3)
{
lean_object* v_u_3453_; lean_object* v_u_3454_; lean_object* v___x_3455_; 
lean_inc_ref(v_body_3452_);
lean_inc_ref(v_binderType_3451_);
lean_dec_ref_known(v_a_3450_, 3);
v_u_3453_ = lean_ctor_get(v_binderType_3451_, 0);
lean_inc(v_u_3453_);
lean_dec_ref_known(v_binderType_3451_, 1);
v_u_3454_ = lean_ctor_get(v_body_3452_, 0);
lean_inc(v_u_3454_);
lean_dec_ref_known(v_body_3452_, 1);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc(v_fst_3413_);
v___x_3455_ = lean_infer_type(v_fst_3413_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
v___x_3457_ = lean_whnf(v_a_3456_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
if (lean_obj_tag(v_a_3458_) == 7)
{
lean_object* v_binderType_3459_; 
v_binderType_3459_ = lean_ctor_get(v_a_3458_, 1);
if (lean_obj_tag(v_binderType_3459_) == 3)
{
lean_object* v_body_3460_; 
v_body_3460_ = lean_ctor_get(v_a_3458_, 2);
if (lean_obj_tag(v_body_3460_) == 3)
{
lean_object* v_u_3461_; lean_object* v_u_3462_; lean_object* v___x_3463_; 
lean_inc_ref(v_body_3460_);
lean_inc_ref(v_binderType_3459_);
lean_dec_ref_known(v_a_3458_, 3);
v_u_3461_ = lean_ctor_get(v_binderType_3459_, 0);
lean_inc(v_u_3461_);
lean_dec_ref_known(v_binderType_3459_, 1);
v_u_3462_ = lean_ctor_get(v_body_3460_, 0);
lean_inc(v_u_3462_);
lean_dec_ref_known(v_body_3460_, 1);
v___x_3463_ = l_Lean_Meta_decLevel(v_u_3453_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = l_Lean_Meta_decLevel(v_u_3461_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
lean_inc(v_a_3464_);
v___x_3467_ = l_Lean_Meta_isLevelDefEq(v_a_3464_, v_a_3466_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3632_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3632_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3632_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_unbox(v_a_3468_);
lean_dec(v_a_3468_);
if (v___x_3472_ == 1)
{
lean_object* v___x_3473_; 
lean_del_object(v___x_3470_);
v___x_3473_ = l_Lean_Meta_decLevel(v_u_3454_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = l_Lean_Meta_decLevel(v_u_3462_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3478_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 1);
lean_ctor_set(v___x_3430_, 1, v___x_3478_);
lean_ctor_set(v___x_3430_, 0, v_a_3476_);
v___x_3480_ = v___x_3430_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3476_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3482_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 1);
lean_ctor_set(v___x_3416_, 1, v___x_3480_);
lean_ctor_set(v___x_3416_, 0, v_a_3474_);
v___x_3482_ = v___x_3416_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3474_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_a_3464_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_Expr_const___override(v___x_3477_, v___x_3483_);
v___x_3485_ = lean_unsigned_to_nat(2u);
v___x_3486_ = lean_mk_empty_array_with_capacity(v___x_3485_);
lean_inc(v_fst_3427_);
v___x_3487_ = lean_array_push(v___x_3486_, v_fst_3427_);
lean_inc(v_fst_3413_);
v___x_3488_ = lean_array_push(v___x_3487_, v_fst_3413_);
v___x_3489_ = l_Lean_mkAppN(v___x_3484_, v___x_3488_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = lean_box(0);
v___x_3491_ = l_Lean_Meta_trySynthInstance(v___x_3489_, v___x_3490_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3622_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3622_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3622_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
if (lean_obj_tag(v_a_3492_) == 1)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
lean_del_object(v___x_3494_);
v_a_3496_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v_a_3492_, 1);
lean_inc(v_snd_3428_);
v___x_3497_ = l_Lean_Meta_getDecLevel(v_snd_3428_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_Lean_Meta_getDecLevel(v_a_3400_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
lean_inc(v_a_3393_);
v___x_3501_ = l_Lean_Meta_getDecLevel(v_a_3393_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3504_, 0, v_a_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3478_);
v___x_3505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3505_, 0, v_a_3500_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3506_, 0, v_a_3498_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
lean_inc_ref(v___x_3506_);
v___x_3507_ = l_Lean_mkConst(v___x_3503_, v___x_3506_);
v___x_3508_ = lean_unsigned_to_nat(5u);
v___x_3509_ = lean_mk_empty_array_with_capacity(v___x_3508_);
lean_inc(v_fst_3427_);
v___x_3510_ = lean_array_push(v___x_3509_, v_fst_3427_);
lean_inc(v_fst_3413_);
v___x_3511_ = lean_array_push(v___x_3510_, v_fst_3413_);
lean_inc(v_a_3496_);
v___x_3512_ = lean_array_push(v___x_3511_, v_a_3496_);
lean_inc(v_snd_3428_);
v___x_3513_ = lean_array_push(v___x_3512_, v_snd_3428_);
lean_inc_ref(v_e_3364_);
v___x_3514_ = lean_array_push(v___x_3513_, v_e_3364_);
v___x_3515_ = l_Lean_mkAppN(v___x_3507_, v___x_3514_);
lean_dec_ref(v___x_3514_);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
lean_inc_ref(v___x_3515_);
v___x_3516_ = lean_infer_type(v___x_3515_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
lean_inc(v_a_3393_);
v___x_3518_ = l_Lean_Meta_isExprDefEq(v_a_3393_, v_a_3517_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3613_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3613_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3613_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_unbox(v_a_3519_);
lean_dec(v_a_3519_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_del_object(v___x_3521_);
lean_dec_ref(v___x_3515_);
lean_del_object(v___x_3425_);
lean_inc(v_fst_3413_);
v___x_3524_ = l_Lean_Meta_isMonad_x3f(v_fst_3413_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3605_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3605_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3605_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
if (lean_obj_tag(v_a_3525_) == 1)
{
lean_object* v_val_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3601_; 
lean_del_object(v___x_3527_);
v_val_3529_ = lean_ctor_get(v_a_3525_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_a_3525_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3531_ = v_a_3525_;
v_isShared_3532_ = v_isSharedCheck_3601_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_val_3529_);
lean_dec(v_a_3525_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3601_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; 
lean_inc(v_snd_3428_);
v___x_3533_ = l_Lean_Meta_getLevel(v_snd_3428_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
lean_inc(v_snd_3414_);
v___x_3535_ = l_Lean_Meta_getLevel(v_snd_3414_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___x_3537_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3538_ = 0;
v___x_3539_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_a_3536_);
lean_ctor_set(v___x_3540_, 1, v___x_3478_);
v___x_3541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_a_3534_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l_Lean_mkConst(v___x_3539_, v___x_3541_);
v___x_3543_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3544_ = lean_unsigned_to_nat(3u);
v___x_3545_ = lean_mk_empty_array_with_capacity(v___x_3544_);
lean_inc_n(v_snd_3428_, 2);
v___x_3546_ = lean_array_push(v___x_3545_, v_snd_3428_);
v___x_3547_ = lean_array_push(v___x_3546_, v___x_3543_);
lean_inc(v_snd_3414_);
v___x_3548_ = lean_array_push(v___x_3547_, v_snd_3414_);
v___x_3549_ = l_Lean_mkAppN(v___x_3542_, v___x_3548_);
lean_dec_ref(v___x_3548_);
v___x_3550_ = l_Lean_mkForall(v___x_3537_, v___x_3538_, v_snd_3428_, v___x_3549_);
v___x_3551_ = l_Lean_Meta_trySynthInstance(v___x_3550_, v___x_3490_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3597_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3597_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3597_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
if (lean_obj_tag(v_a_3552_) == 1)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_del_object(v___x_3554_);
v_a_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v_a_3552_, 1);
v___x_3557_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3558_ = l_Lean_mkConst(v___x_3557_, v___x_3506_);
v___x_3559_ = lean_unsigned_to_nat(8u);
v___x_3560_ = lean_mk_empty_array_with_capacity(v___x_3559_);
v___x_3561_ = lean_array_push(v___x_3560_, v_fst_3427_);
v___x_3562_ = lean_array_push(v___x_3561_, v_fst_3413_);
v___x_3563_ = lean_array_push(v___x_3562_, v_snd_3428_);
v___x_3564_ = lean_array_push(v___x_3563_, v_snd_3414_);
v___x_3565_ = lean_array_push(v___x_3564_, v_a_3496_);
v___x_3566_ = lean_array_push(v___x_3565_, v_a_3556_);
v___x_3567_ = lean_array_push(v___x_3566_, v_val_3529_);
v___x_3568_ = lean_array_push(v___x_3567_, v_e_3364_);
v___x_3569_ = l_Lean_mkAppN(v___x_3558_, v___x_3568_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = l_Lean_Meta_expandCoe(v___x_3569_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v_fst_3572_; lean_object* v___x_3573_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v_fst_3572_ = lean_ctor_get(v_a_3571_, 0);
lean_inc_n(v_fst_3572_, 2);
lean_dec(v_a_3571_);
lean_inc(v_a_3369_);
lean_inc_ref(v_a_3368_);
lean_inc(v_a_3367_);
lean_inc_ref(v_a_3366_);
v___x_3573_ = lean_infer_type(v_fst_3572_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = l_Lean_Meta_isExprDefEq(v_a_3393_, v_a_3574_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3590_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3590_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3590_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_unbox(v_a_3576_);
lean_dec(v_a_3576_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3582_; 
lean_dec(v_fst_3572_);
lean_del_object(v___x_3531_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3490_);
v___x_3582_ = v___x_3578_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3490_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
else
{
lean_object* v___x_3585_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_fst_3572_);
v___x_3585_ = v___x_3531_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_fst_3572_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3585_);
v___x_3587_ = v___x_3578_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
else
{
lean_object* v_a_3591_; 
lean_dec(v_fst_3572_);
lean_del_object(v___x_3531_);
v_a_3591_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3575_, 1);
v_a_3378_ = v_a_3591_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3592_; 
lean_dec(v_fst_3572_);
lean_del_object(v___x_3531_);
lean_dec(v_a_3393_);
v_a_3592_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3573_, 1);
v_a_3378_ = v_a_3592_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3593_; 
lean_del_object(v___x_3531_);
lean_dec(v_a_3393_);
v_a_3593_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3570_, 1);
v_a_3378_ = v_a_3593_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3595_; 
lean_dec(v_a_3552_);
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3490_);
v___x_3595_ = v___x_3554_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3490_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_object* v_a_3598_; 
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3598_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3551_, 1);
v_a_3378_ = v_a_3598_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3599_; 
lean_dec(v_a_3534_);
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3599_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3535_, 1);
v_a_3378_ = v_a_3599_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3600_; 
lean_del_object(v___x_3531_);
lean_dec(v_val_3529_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3600_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3533_, 1);
v_a_3378_ = v_a_3600_;
goto v___jp_3377_;
}
}
}
else
{
lean_object* v___x_3603_; 
lean_dec(v_a_3525_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3490_);
v___x_3603_ = v___x_3527_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3490_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_a_3606_; 
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3606_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3524_, 1);
v_a_3378_ = v_a_3606_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3608_; 
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3515_);
v___x_3608_ = v___x_3425_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3515_);
v___x_3608_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3608_);
v___x_3610_ = v___x_3521_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
else
{
lean_object* v_a_3614_; 
lean_dec_ref(v___x_3515_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3614_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3518_, 1);
v_a_3378_ = v_a_3614_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3615_; 
lean_dec_ref(v___x_3515_);
lean_dec_ref_known(v___x_3506_, 2);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3615_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3516_, 1);
v_a_3378_ = v_a_3615_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3616_; 
lean_dec(v_a_3500_);
lean_dec(v_a_3498_);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3616_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3501_, 1);
v_a_3378_ = v_a_3616_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3617_; 
lean_dec(v_a_3498_);
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3617_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3499_, 1);
v_a_3378_ = v_a_3617_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3618_; 
lean_dec(v_a_3496_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3618_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3497_, 1);
v_a_3378_ = v_a_3618_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3620_; 
lean_dec(v_a_3492_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3490_);
v___x_3620_ = v___x_3494_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3490_);
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
lean_object* v_a_3623_; 
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3623_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3491_, 1);
v_a_3378_ = v_a_3623_;
goto v___jp_3377_;
}
}
}
}
else
{
lean_object* v_a_3626_; 
lean_dec(v_a_3474_);
lean_dec(v_a_3464_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3626_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3475_, 1);
v_a_3378_ = v_a_3626_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3627_; 
lean_dec(v_a_3464_);
lean_dec(v_u_3462_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3627_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3473_, 1);
v_a_3378_ = v_a_3627_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
lean_dec(v_a_3464_);
lean_dec(v_u_3462_);
lean_dec(v_u_3454_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3628_ = lean_box(0);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3628_);
v___x_3630_ = v___x_3470_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; 
lean_dec(v_a_3464_);
lean_dec(v_u_3462_);
lean_dec(v_u_3454_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3633_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3467_, 1);
v_a_3378_ = v_a_3633_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3634_; 
lean_dec(v_a_3464_);
lean_dec(v_u_3462_);
lean_dec(v_u_3454_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3634_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3465_, 1);
v_a_3378_ = v_a_3634_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3635_; 
lean_dec(v_u_3462_);
lean_dec(v_u_3461_);
lean_dec(v_u_3454_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3635_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3463_, 1);
v_a_3378_ = v_a_3635_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3636_; 
lean_dec(v_u_3454_);
lean_dec(v_u_3453_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3636_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3458_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec_ref_known(v_a_3458_, 3);
v___y_3382_ = v___x_3636_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3637_; 
lean_dec(v_u_3454_);
lean_dec(v_u_3453_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3637_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3458_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec_ref_known(v_a_3458_, 3);
v___y_3382_ = v___x_3637_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec(v_u_3454_);
lean_dec(v_u_3453_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3638_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3458_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3458_);
v___y_3382_ = v___x_3638_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3639_; 
lean_dec(v_u_3454_);
lean_dec(v_u_3453_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3639_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3457_, 1);
v_a_3378_ = v_a_3639_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3640_; 
lean_dec(v_u_3454_);
lean_dec(v_u_3453_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3640_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3455_, 1);
v_a_3378_ = v_a_3640_;
goto v___jp_3377_;
}
}
else
{
lean_object* v___x_3641_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3641_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3450_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec_ref_known(v_a_3450_, 3);
v___y_3382_ = v___x_3641_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3642_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3642_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3450_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec_ref_known(v_a_3450_, 3);
v___y_3382_ = v___x_3642_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3643_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3643_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3450_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3450_);
v___y_3382_ = v___x_3643_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3644_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3644_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3449_, 1);
v_a_3378_ = v_a_3644_;
goto v___jp_3377_;
}
}
else
{
lean_object* v_a_3645_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3645_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3447_, 1);
v_a_3378_ = v_a_3645_;
goto v___jp_3377_;
}
}
}
else
{
lean_object* v___x_3646_; 
lean_del_object(v___x_3437_);
lean_del_object(v___x_3430_);
lean_del_object(v___x_3416_);
lean_dec(v_a_3400_);
lean_dec(v_a_3393_);
v___x_3646_ = l_Lean_Meta_isMonad_x3f(v_fst_3413_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3739_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3739_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3739_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
if (lean_obj_tag(v_a_3647_) == 1)
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3651_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v_fst_3427_);
v___x_3653_ = v___x_3425_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_fst_3427_);
v___x_3653_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3655_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v_snd_3428_);
v___x_3655_ = v___x_3411_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_snd_3428_);
v___x_3655_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 1);
lean_ctor_set(v___x_3402_, 0, v_snd_3414_);
v___x_3657_ = v___x_3402_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_snd_3414_);
v___x_3657_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___y_3660_; uint8_t v___y_3661_; lean_object* v_a_3683_; lean_object* v___x_3687_; 
v___x_3658_ = lean_box(0);
if (v_isShared_3396_ == 0)
{
lean_ctor_set_tag(v___x_3395_, 1);
lean_ctor_set(v___x_3395_, 0, v_e_3364_);
v___x_3687_ = v___x_3395_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_e_3364_);
v___x_3687_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3686_;
}
v___jp_3659_:
{
if (v___y_3661_ == 0)
{
lean_object* v___x_3662_; 
lean_dec_ref(v___y_3660_);
lean_del_object(v___x_3649_);
v___x_3662_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3433_, v_a_3367_, v_a_3369_);
lean_dec(v_a_3433_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v___x_3662_, 0);
lean_dec(v_unused_3670_);
v___x_3664_ = v___x_3662_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v___x_3662_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3658_);
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3658_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_a_3671_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3662_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3662_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v___x_3680_; 
lean_dec(v_a_3433_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 1);
lean_ctor_set(v___x_3649_, 0, v___y_3660_);
v___x_3680_ = v___x_3649_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___y_3660_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
v___jp_3682_:
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_Exception_isInterrupt(v_a_3683_);
if (v___x_3684_ == 0)
{
uint8_t v___x_3685_; 
lean_inc_ref(v_a_3683_);
v___x_3685_ = l_Lean_Exception_isRuntime(v_a_3683_);
v___y_3660_ = v_a_3683_;
v___y_3661_ = v___x_3685_;
goto v___jp_3659_;
}
else
{
v___y_3660_ = v_a_3683_;
v___y_3661_ = v___x_3684_;
goto v___jp_3659_;
}
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3688_ = lean_unsigned_to_nat(6u);
v___x_3689_ = lean_mk_empty_array_with_capacity(v___x_3688_);
v___x_3690_ = lean_array_push(v___x_3689_, v___x_3653_);
v___x_3691_ = lean_array_push(v___x_3690_, v___x_3655_);
v___x_3692_ = lean_array_push(v___x_3691_, v___x_3657_);
v___x_3693_ = lean_array_push(v___x_3692_, v___x_3658_);
v___x_3694_ = lean_array_push(v___x_3693_, v_a_3647_);
v___x_3695_ = lean_array_push(v___x_3694_, v___x_3687_);
v___x_3696_ = l_Lean_Meta_mkAppOptM(v___x_3651_, v___x_3695_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3715_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3715_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3715_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Meta_expandCoe(v_a_3697_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3713_; 
lean_del_object(v___x_3649_);
lean_dec(v_a_3433_);
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3713_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3713_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_fst_3706_; lean_object* v___x_3708_; 
v_fst_3706_ = lean_ctor_get(v_a_3702_, 0);
lean_inc(v_fst_3706_);
lean_dec(v_a_3702_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set_tag(v___x_3699_, 1);
lean_ctor_set(v___x_3699_, 0, v_fst_3706_);
v___x_3708_ = v___x_3699_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_fst_3706_);
v___x_3708_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3708_);
v___x_3710_ = v___x_3704_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
else
{
lean_object* v_a_3714_; 
lean_del_object(v___x_3699_);
v_a_3714_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3701_, 1);
v_a_3683_ = v_a_3714_;
goto v___jp_3682_;
}
}
}
else
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3696_, 1);
v_a_3683_ = v_a_3716_;
goto v___jp_3682_;
}
}
}
}
}
}
else
{
lean_object* v___x_3721_; 
lean_del_object(v___x_3649_);
lean_dec(v_a_3647_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_del_object(v___x_3395_);
lean_dec_ref(v_e_3364_);
v___x_3721_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3433_, v_a_3367_, v_a_3369_);
lean_dec(v_a_3433_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3729_; 
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v___x_3721_, 0);
lean_dec(v_unused_3730_);
v___x_3723_ = v___x_3721_;
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
else
{
lean_dec(v___x_3721_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_box(0);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3721_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3721_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3433_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_dec(v_snd_3414_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_del_object(v___x_3395_);
lean_dec_ref(v_e_3364_);
return v___x_3646_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_a_3433_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3741_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3434_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3434_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
lean_del_object(v___x_3425_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3749_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3432_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3432_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_dec(v_a_3419_);
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3759_ = lean_box(0);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3759_);
v___x_3761_ = v___x_3421_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3759_);
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
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
lean_dec(v_fst_3413_);
lean_del_object(v___x_3411_);
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3764_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3418_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3418_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec(v_a_3405_);
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v___x_3774_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3774_);
v___x_3776_ = v___x_3407_;
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
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3779_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3404_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3404_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
lean_dec_ref(v_e_3364_);
v_a_3788_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3397_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3397_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3797_, lean_object* v_expectedType_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3797_, v_expectedType_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3805_, lean_object* v_expectedType_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v___x_3812_; 
lean_inc_ref(v_expectedType_3806_);
lean_inc_ref(v_expr_3805_);
v___x_3812_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3805_, v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3892_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3815_ = v___x_3812_;
v_isShared_3816_ = v_isSharedCheck_3892_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3892_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
if (lean_obj_tag(v_a_3813_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_val_3817_ = lean_ctor_get(v_a_3813_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_a_3813_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3819_ = v_a_3813_;
v_isShared_3820_ = v_isSharedCheck_3829_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_val_3817_);
lean_dec(v_a_3813_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3829_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v_val_3817_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3822_);
v___x_3824_ = v___x_3819_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3826_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3824_);
v___x_3826_ = v___x_3815_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v___x_3830_; 
lean_del_object(v___x_3815_);
lean_dec(v_a_3813_);
lean_inc_ref(v_expectedType_3806_);
v___x_3830_ = l_Lean_Meta_whnfR(v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; uint8_t v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = l_Lean_Expr_isForall(v_a_3831_);
lean_dec(v_a_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3805_, v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_3833_;
}
else
{
lean_object* v___x_3834_; 
lean_inc_ref(v_expr_3805_);
v___x_3834_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3805_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
if (lean_obj_tag(v_a_3835_) == 1)
{
lean_object* v_val_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3874_; 
v_val_3836_ = lean_ctor_get(v_a_3835_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_a_3835_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3838_ = v_a_3835_;
v_isShared_3839_ = v_isSharedCheck_3874_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_val_3836_);
lean_dec(v_a_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3874_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; 
lean_inc(v_a_3810_);
lean_inc_ref(v_a_3809_);
lean_inc(v_a_3808_);
lean_inc_ref(v_a_3807_);
lean_inc(v_val_3836_);
v___x_3840_ = lean_infer_type(v_val_3836_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
lean_inc_ref(v_expectedType_3806_);
v___x_3842_ = l_Lean_Meta_isExprDefEq(v_a_3841_, v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3857_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3857_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3857_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_unbox(v_a_3843_);
lean_dec(v_a_3843_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_del_object(v___x_3845_);
lean_del_object(v___x_3838_);
lean_dec(v_val_3836_);
v___x_3848_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3805_, v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_3848_;
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3852_; 
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v_val_3836_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3850_);
v___x_3852_ = v___x_3838_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3852_);
v___x_3854_ = v___x_3845_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
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
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_del_object(v___x_3838_);
lean_dec(v_val_3836_);
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_a_3858_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3842_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3842_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_del_object(v___x_3838_);
lean_dec(v_val_3836_);
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_a_3866_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3840_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3840_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
else
{
lean_object* v___x_3875_; 
lean_dec(v_a_3835_);
v___x_3875_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3805_, v_expectedType_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_3875_;
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_a_3876_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3834_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3834_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
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
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_a_3884_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3830_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3830_);
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
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref(v_expectedType_3806_);
lean_dec_ref(v_expr_3805_);
v_a_3893_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3812_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3812_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3901_, lean_object* v_expectedType_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3901_, v_expectedType_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3909_, lean_object* v_expectedType_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3909_, v_expectedType_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3941_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3941_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3941_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
switch(lean_obj_tag(v_a_3917_))
{
case 0:
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = lean_box(0);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3921_);
v___x_3923_ = v___x_3919_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
case 1:
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3936_; 
v_a_3925_ = lean_ctor_get(v_a_3917_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_a_3917_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3927_ = v_a_3917_;
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v_a_3917_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v_fst_3929_; lean_object* v___x_3931_; 
v_fst_3929_ = lean_ctor_get(v_a_3925_, 0);
lean_inc(v_fst_3929_);
lean_dec(v_a_3925_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v_fst_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_fst_3929_);
v___x_3931_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3933_; 
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3931_);
v___x_3933_ = v___x_3919_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
default: 
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_box(2);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3937_);
v___x_3939_ = v___x_3919_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_a_3942_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3916_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3916_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3950_, lean_object* v_expectedType_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_Meta_coerce_x3f(v_expr_3950_, v_expectedType_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3957_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Coe(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
