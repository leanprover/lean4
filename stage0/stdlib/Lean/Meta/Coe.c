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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
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
lean_dec_ref(v_a_115_);
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
lean_object* v_ref_207_; lean_object* v___x_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_255_; 
v_ref_207_ = lean_ctor_get(v___y_204_, 5);
v___x_208_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_200_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_255_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_255_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_255_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v_traceState_214_; lean_object* v_env_215_; lean_object* v_nextMacroScope_216_; lean_object* v_ngen_217_; lean_object* v_auxDeclNGen_218_; lean_object* v_cache_219_; lean_object* v_messages_220_; lean_object* v_infoState_221_; lean_object* v_snapshotTasks_222_; lean_object* v_newDecls_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_254_; 
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
v_newDecls_223_ = lean_ctor_get(v___x_213_, 9);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_254_ == 0)
{
v___x_225_ = v___x_213_;
v_isShared_226_ = v_isSharedCheck_254_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_newDecls_223_);
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
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_254_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint64_t v_tid_227_; lean_object* v_traces_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_253_; 
v_tid_227_ = lean_ctor_get_uint64(v_traceState_214_, sizeof(void*)*1);
v_traces_228_ = lean_ctor_get(v_traceState_214_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_traceState_214_);
if (v_isSharedCheck_253_ == 0)
{
v___x_230_ = v_traceState_214_;
v_isShared_231_ = v_isSharedCheck_253_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_traces_228_);
lean_dec(v_traceState_214_);
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
lean_ctor_set(v___x_236_, 0, v_cls_199_);
lean_ctor_set(v___x_236_, 1, v___x_232_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3, v___x_233_);
lean_ctor_set_float(v___x_236_, sizeof(void*)*3 + 8, v___x_233_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 16, v___x_234_);
v___x_237_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2));
v___x_238_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v_a_209_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
lean_inc(v_ref_207_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_207_);
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
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_env_215_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_nextMacroScope_216_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_ngen_217_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_auxDeclNGen_218_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_251_, 5, v_cache_219_);
lean_ctor_set(v_reuseFailAlloc_251_, 6, v_messages_220_);
lean_ctor_set(v_reuseFailAlloc_251_, 7, v_infoState_221_);
lean_ctor_set(v_reuseFailAlloc_251_, 8, v_snapshotTasks_222_);
lean_ctor_set(v_reuseFailAlloc_251_, 9, v_newDecls_223_);
v___x_244_ = v_reuseFailAlloc_251_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = lean_st_ref_set(v___y_205_, v___x_244_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_201_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_247_);
v___x_249_ = v___x_211_;
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
return v___x_271_;
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; 
v___x_280_ = ((size_t)5ULL);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_shift_left(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_285_ = lean_usize_sub(v___x_284_, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_286_, size_t v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v_es_289_; lean_object* v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v_j_294_; lean_object* v___x_295_; 
v_es_289_ = lean_ctor_get(v_x_286_, 0);
v___x_290_ = lean_box(2);
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_293_ = lean_usize_land(v_x_287_, v___x_292_);
v_j_294_ = lean_usize_to_nat(v___x_293_);
v___x_295_ = lean_array_get_borrowed(v___x_290_, v_es_289_, v_j_294_);
lean_dec(v_j_294_);
switch(lean_obj_tag(v___x_295_))
{
case 0:
{
lean_object* v_key_296_; uint8_t v___x_297_; 
v_key_296_ = lean_ctor_get(v___x_295_, 0);
v___x_297_ = l_Lean_instBEqExtraModUse_beq(v_x_288_, v_key_296_);
return v___x_297_;
}
case 1:
{
lean_object* v_node_298_; size_t v___x_299_; 
v_node_298_ = lean_ctor_get(v___x_295_, 0);
v___x_299_ = lean_usize_shift_right(v_x_287_, v___x_291_);
v_x_286_ = v_node_298_;
v_x_287_ = v___x_299_;
goto _start;
}
default: 
{
uint8_t v___x_301_; 
v___x_301_ = 0;
return v___x_301_;
}
}
}
else
{
lean_object* v_ks_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_ks_302_ = lean_ctor_get(v_x_286_, 0);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_302_, v___x_303_, v_x_288_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
size_t v_x_37520__boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_x_37520__boxed_308_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_res_309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_305_, v_x_37520__boxed_308_, v_x_307_);
lean_dec_ref(v_x_307_);
lean_dec_ref(v_x_305_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint64_t v___x_313_; size_t v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Lean_instHashableExtraModUse_hash(v_x_312_);
v___x_314_ = lean_uint64_to_usize(v___x_313_);
v___x_315_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_311_, v___x_314_, v_x_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_316_, v_x_317_);
lean_dec_ref(v_x_317_);
lean_dec_ref(v_x_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1));
v___x_323_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0));
v___x_324_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_331_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
lean_ctor_set(v___x_331_, 3, v___x_330_);
lean_ctor_set(v___x_331_, 4, v___x_330_);
lean_ctor_set(v___x_331_, 5, v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_337_ = l_Lean_stringToMessageData(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11));
v___x_340_ = l_Lean_stringToMessageData(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_cls_346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_347_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_348_ = l_Lean_Name_append(v___x_347_, v_cls_346_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_359_, uint8_t v_isMeta_360_, lean_object* v_hint_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v_env_369_; uint8_t v_isExporting_370_; lean_object* v___x_371_; lean_object* v_env_372_; lean_object* v___x_373_; lean_object* v_entry_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_368_ = lean_st_ref_get(v___y_366_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_env_369_);
lean_dec(v___x_368_);
v_isExporting_370_ = lean_ctor_get_uint8(v_env_369_, sizeof(void*)*8);
lean_dec_ref(v_env_369_);
v___x_371_ = lean_st_ref_get(v___y_366_);
v_env_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc_ref(v_env_372_);
lean_dec(v___x_371_);
v___x_373_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
lean_inc(v_mod_359_);
v_entry_374_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_374_, 0, v_mod_359_);
lean_ctor_set_uint8(v_entry_374_, sizeof(void*)*1, v_isExporting_370_);
lean_ctor_set_uint8(v_entry_374_, sizeof(void*)*1 + 1, v_isMeta_360_);
v___x_375_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_376_ = lean_box(1);
v___x_377_ = lean_box(0);
v___x_423_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_373_, v___x_375_, v_env_372_, v___x_376_, v___x_377_);
v___x_424_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_423_, v_entry_374_);
lean_dec(v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v_options_425_; uint8_t v_hasTrace_426_; 
v_options_425_ = lean_ctor_get(v___y_365_, 2);
v_hasTrace_426_ = lean_ctor_get_uint8(v_options_425_, sizeof(void*)*1);
if (v_hasTrace_426_ == 0)
{
lean_dec(v_hint_361_);
lean_dec(v_mod_359_);
v___y_379_ = v___y_362_;
v___y_380_ = v___y_364_;
v___y_381_ = v___y_366_;
goto v___jp_378_;
}
else
{
lean_object* v_inheritedTraceOptions_427_; lean_object* v_cls_428_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_inheritedTraceOptions_427_ = lean_ctor_get(v___y_365_, 13);
v_cls_428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_427_, v_options_425_, v___x_450_);
if (v___x_451_ == 0)
{
lean_dec(v_hint_361_);
lean_dec(v_mod_359_);
v___y_379_ = v___y_362_;
v___y_380_ = v___y_364_;
v___y_381_ = v___y_366_;
goto v___jp_378_;
}
else
{
lean_object* v___x_452_; lean_object* v___y_454_; 
v___x_452_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_370_ == 0)
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_454_ = v___x_462_;
goto v___jp_453_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc_ref(v___y_454_);
v___x_455_ = l_Lean_stringToMessageData(v___y_454_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_452_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
if (v_isMeta_360_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_437_ = v___x_458_;
v___y_438_ = v___x_459_;
goto v___jp_436_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_437_ = v___x_458_;
v___y_438_ = v___x_460_;
goto v___jp_436_;
}
}
}
v___jp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___y_430_);
lean_ctor_set(v___x_432_, 1, v___y_431_);
v___x_433_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_428_, v___x_432_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v_snd_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref(v___x_433_);
v_snd_435_ = lean_ctor_get(v_a_434_, 1);
lean_inc(v_snd_435_);
lean_dec(v_a_434_);
v___y_379_ = v_snd_435_;
v___y_380_ = v___y_364_;
v___y_381_ = v___y_366_;
goto v___jp_378_;
}
else
{
lean_dec_ref(v_entry_374_);
return v___x_433_;
}
}
v___jp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
lean_inc_ref(v___y_438_);
v___x_439_ = l_Lean_stringToMessageData(v___y_438_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___y_437_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_MessageData_ofName(v_mod_359_);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_Name_isAnonymous(v_hint_361_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_447_ = l_Lean_MessageData_ofName(v_hint_361_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___y_430_ = v___x_444_;
v___y_431_ = v___x_448_;
goto v___jp_429_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_hint_361_);
v___x_449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_430_ = v___x_444_;
v___y_431_ = v___x_449_;
goto v___jp_429_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v_entry_374_);
lean_dec(v_hint_361_);
lean_dec(v_mod_359_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___y_362_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
v___jp_378_:
{
lean_object* v___x_382_; lean_object* v_toEnvExtension_383_; lean_object* v_env_384_; lean_object* v_nextMacroScope_385_; lean_object* v_ngen_386_; lean_object* v_auxDeclNGen_387_; lean_object* v_traceState_388_; lean_object* v_messages_389_; lean_object* v_infoState_390_; lean_object* v_snapshotTasks_391_; lean_object* v_newDecls_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_421_; 
v___x_382_ = lean_st_ref_take(v___y_381_);
v_toEnvExtension_383_ = lean_ctor_get(v___x_375_, 0);
v_env_384_ = lean_ctor_get(v___x_382_, 0);
v_nextMacroScope_385_ = lean_ctor_get(v___x_382_, 1);
v_ngen_386_ = lean_ctor_get(v___x_382_, 2);
v_auxDeclNGen_387_ = lean_ctor_get(v___x_382_, 3);
v_traceState_388_ = lean_ctor_get(v___x_382_, 4);
v_messages_389_ = lean_ctor_get(v___x_382_, 6);
v_infoState_390_ = lean_ctor_get(v___x_382_, 7);
v_snapshotTasks_391_ = lean_ctor_get(v___x_382_, 8);
v_newDecls_392_ = lean_ctor_get(v___x_382_, 9);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_382_, 5);
lean_dec(v_unused_422_);
v___x_394_ = v___x_382_;
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_newDecls_392_);
lean_inc(v_snapshotTasks_391_);
lean_inc(v_infoState_390_);
lean_inc(v_messages_389_);
lean_inc(v_traceState_388_);
lean_inc(v_auxDeclNGen_387_);
lean_inc(v_ngen_386_);
lean_inc(v_nextMacroScope_385_);
lean_inc(v_env_384_);
lean_dec(v___x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_421_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_asyncMode_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v_asyncMode_396_ = lean_ctor_get(v_toEnvExtension_383_, 2);
v___x_397_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_375_, v_env_384_, v_entry_374_, v_asyncMode_396_, v___x_377_);
v___x_398_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 5, v___x_398_);
lean_ctor_set(v___x_394_, 0, v___x_397_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_nextMacroScope_385_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_ngen_386_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_auxDeclNGen_387_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_traceState_388_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_messages_389_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_infoState_390_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_snapshotTasks_391_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_newDecls_392_);
v___x_400_ = v_reuseFailAlloc_420_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_mctx_403_; lean_object* v_zetaDeltaFVarIds_404_; lean_object* v_postponed_405_; lean_object* v_diag_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_418_; 
v___x_401_ = lean_st_ref_set(v___y_381_, v___x_400_);
v___x_402_ = lean_st_ref_take(v___y_380_);
v_mctx_403_ = lean_ctor_get(v___x_402_, 0);
v_zetaDeltaFVarIds_404_ = lean_ctor_get(v___x_402_, 2);
v_postponed_405_ = lean_ctor_get(v___x_402_, 3);
v_diag_406_ = lean_ctor_get(v___x_402_, 4);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_402_, 1);
lean_dec(v_unused_419_);
v___x_408_ = v___x_402_;
v_isShared_409_ = v_isSharedCheck_418_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_diag_406_);
lean_inc(v_postponed_405_);
lean_inc(v_zetaDeltaFVarIds_404_);
lean_inc(v_mctx_403_);
lean_dec(v___x_402_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_418_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_mctx_403_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_zetaDeltaFVarIds_404_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_postponed_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_diag_406_);
v___x_412_ = v_reuseFailAlloc_417_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_st_ref_set(v___y_380_, v___x_412_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___y_379_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_466_, lean_object* v_isMeta_467_, lean_object* v_hint_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
uint8_t v_isMeta_boxed_475_; lean_object* v_res_476_; 
v_isMeta_boxed_475_ = lean_unbox(v_isMeta_467_);
v_res_476_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_466_, v_isMeta_boxed_475_, v_hint_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_box(0);
return v___x_479_;
}
else
{
lean_object* v_key_480_; lean_object* v_value_481_; lean_object* v_tail_482_; uint8_t v___x_483_; 
v_key_480_ = lean_ctor_get(v_x_478_, 0);
v_value_481_ = lean_ctor_get(v_x_478_, 1);
v_tail_482_ = lean_ctor_get(v_x_478_, 2);
v___x_483_ = lean_name_eq(v_key_480_, v_a_477_);
if (v___x_483_ == 0)
{
v_x_478_ = v_tail_482_;
goto _start;
}
else
{
lean_object* v___x_485_; 
lean_inc(v_value_481_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_value_481_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_486_, v_x_487_);
lean_dec(v_x_487_);
lean_dec(v_a_486_);
return v_res_488_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_489_; uint64_t v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1723u);
v___x_490_ = lean_uint64_of_nat(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_buckets_493_; lean_object* v___x_494_; uint64_t v___y_496_; 
v_buckets_493_ = lean_ctor_get(v_m_491_, 1);
v___x_494_ = lean_array_get_size(v_buckets_493_);
if (lean_obj_tag(v_a_492_) == 0)
{
uint64_t v___x_510_; 
v___x_510_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
v___y_496_ = v___x_510_;
goto v___jp_495_;
}
else
{
uint64_t v_hash_511_; 
v_hash_511_ = lean_ctor_get_uint64(v_a_492_, sizeof(void*)*2);
v___y_496_ = v_hash_511_;
goto v___jp_495_;
}
v___jp_495_:
{
uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v_fold_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_497_ = 32ULL;
v___x_498_ = lean_uint64_shift_right(v___y_496_, v___x_497_);
v_fold_499_ = lean_uint64_xor(v___y_496_, v___x_498_);
v___x_500_ = 16ULL;
v___x_501_ = lean_uint64_shift_right(v_fold_499_, v___x_500_);
v___x_502_ = lean_uint64_xor(v_fold_499_, v___x_501_);
v___x_503_ = lean_uint64_to_usize(v___x_502_);
v___x_504_ = lean_usize_of_nat(v___x_494_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_sub(v___x_504_, v___x_505_);
v___x_507_ = lean_usize_land(v___x_503_, v___x_506_);
v___x_508_ = lean_array_uget_borrowed(v_buckets_493_, v___x_507_);
v___x_509_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_492_, v___x_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_515_, lean_object* v_declName_516_, lean_object* v_as_517_, size_t v_sz_518_, size_t v_i_519_, lean_object* v_b_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_declName_516_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_b_520_);
lean_ctor_set(v___x_528_, 1, v___y_521_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; lean_object* v_modules_531_; lean_object* v___x_532_; lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v_toImport_535_; lean_object* v_module_536_; uint8_t v___x_537_; lean_object* v___x_538_; 
v___x_530_ = l_Lean_Environment_header(v___x_515_);
v_modules_531_ = lean_ctor_get(v___x_530_, 3);
lean_inc_ref(v_modules_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_533_ = lean_array_uget_borrowed(v_as_517_, v_i_519_);
v___x_534_ = lean_array_get(v___x_532_, v_modules_531_, v_a_533_);
lean_dec_ref(v_modules_531_);
v_toImport_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_toImport_535_);
lean_dec(v___x_534_);
v_module_536_ = lean_ctor_get(v_toImport_535_, 0);
lean_inc(v_module_536_);
lean_dec_ref(v_toImport_535_);
v___x_537_ = 0;
lean_inc(v_declName_516_);
v___x_538_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_536_, v___x_537_, v_declName_516_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_snd_540_; lean_object* v___x_541_; size_t v___x_542_; size_t v___x_543_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref(v___x_538_);
v_snd_540_ = lean_ctor_get(v_a_539_, 1);
lean_inc(v_snd_540_);
lean_dec(v_a_539_);
v___x_541_ = lean_box(0);
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_519_, v___x_542_);
v_i_519_ = v___x_543_;
v_b_520_ = v___x_541_;
v___y_521_ = v_snd_540_;
goto _start;
}
else
{
lean_dec(v_declName_516_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_545_, lean_object* v_declName_546_, lean_object* v_as_547_, lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_558_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_545_, v_declName_546_, v_as_547_, v_sz_boxed_557_, v_i_boxed_558_, v_b_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v_as_547_);
lean_dec_ref(v___x_545_);
return v_res_559_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_563_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_564_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_563_, v___x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_567_, uint8_t v_isMeta_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_env_580_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___x_605_; 
v___x_575_ = lean_st_ref_get(v___y_573_);
v_env_580_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_580_);
lean_dec(v___x_575_);
v___x_605_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_580_, v_declName_567_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec_ref(v_env_580_);
lean_dec(v_declName_567_);
goto v___jp_576_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_607_; lean_object* v_modules_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref(v___x_605_);
v___x_607_ = l_Lean_Environment_header(v_env_580_);
v_modules_608_ = lean_ctor_get(v___x_607_, 3);
lean_inc_ref(v_modules_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = lean_array_get_size(v_modules_608_);
v___x_610_ = lean_nat_dec_lt(v_val_606_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v_modules_608_);
lean_dec(v_val_606_);
lean_dec_ref(v_env_580_);
lean_dec(v_declName_567_);
goto v___jp_576_;
}
else
{
lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___y_616_; 
v___x_611_ = lean_st_ref_get(v___y_573_);
v_env_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc_ref(v_env_612_);
lean_dec(v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_614_ = lean_array_fget(v_modules_608_, v_val_606_);
lean_dec(v_val_606_);
lean_dec_ref(v_modules_608_);
if (v_isMeta_568_ == 0)
{
lean_dec_ref(v_env_612_);
v___y_616_ = v_isMeta_568_;
goto v___jp_615_;
}
else
{
uint8_t v___x_629_; 
lean_inc(v_declName_567_);
v___x_629_ = l_Lean_isMarkedMeta(v_env_612_, v_declName_567_);
if (v___x_629_ == 0)
{
v___y_616_ = v_isMeta_568_;
goto v___jp_615_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = 0;
v___y_616_ = v___x_630_;
goto v___jp_615_;
}
}
v___jp_615_:
{
lean_object* v_toImport_617_; lean_object* v_module_618_; lean_object* v___x_619_; 
v_toImport_617_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_toImport_617_);
lean_dec(v___x_614_);
v_module_618_ = lean_ctor_get(v_toImport_617_, 0);
lean_inc(v_module_618_);
lean_dec_ref(v_toImport_617_);
lean_inc(v_declName_567_);
v___x_619_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_618_, v___y_616_, v_declName_567_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_snd_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_619_);
v_snd_621_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_621_);
lean_dec(v_a_620_);
v___x_622_ = l_Lean_indirectModUseExt;
v___x_623_ = lean_box(1);
v___x_624_ = lean_box(0);
lean_inc_ref(v_env_580_);
v___x_625_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_613_, v___x_622_, v_env_580_, v___x_623_, v___x_624_);
v___x_626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_625_, v_declName_567_);
lean_dec(v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_582_ = v_snd_621_;
v___y_583_ = v___x_627_;
goto v___jp_581_;
}
else
{
lean_object* v_val_628_; 
v_val_628_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_628_);
lean_dec_ref(v___x_626_);
v___y_582_ = v_snd_621_;
v___y_583_ = v_val_628_;
goto v___jp_581_;
}
}
else
{
lean_dec_ref(v_env_580_);
lean_dec(v_declName_567_);
return v___x_619_;
}
}
}
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___y_569_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
v___jp_581_:
{
lean_object* v___x_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_584_ = lean_box(0);
v_sz_585_ = lean_array_size(v___y_583_);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_580_, v_declName_567_, v___y_583_, v_sz_585_, v___x_586_, v___x_584_, v___y_582_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_env_580_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_604_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_604_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_604_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_604_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_602_; 
v_snd_592_ = lean_ctor_get(v_a_588_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_a_588_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_a_588_, 0);
lean_dec(v_unused_603_);
v___x_594_ = v_a_588_;
v_isShared_595_ = v_isSharedCheck_602_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_dec(v_a_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_602_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_584_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_snd_592_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_599_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_599_ = v___x_590_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
else
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_631_, lean_object* v_isMeta_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v_isMeta_boxed_639_; lean_object* v_res_640_; 
v_isMeta_boxed_639_ = lean_unbox(v_isMeta_632_);
v_res_640_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_631_, v_isMeta_boxed_639_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___y_656_; lean_object* v_f_660_; uint8_t v___x_661_; 
v_f_660_ = l_Lean_Expr_getAppFn(v_e_648_);
v___x_661_ = l_Lean_Expr_isConst(v_f_660_);
if (v___x_661_ == 0)
{
lean_dec_ref(v_f_660_);
lean_dec_ref(v_e_648_);
v___y_656_ = v___y_649_;
goto v___jp_655_;
}
else
{
lean_object* v___x_662_; lean_object* v_env_663_; lean_object* v_declName_664_; uint8_t v___x_665_; 
v___x_662_ = lean_st_ref_get(v___y_653_);
v_env_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_env_663_);
lean_dec(v___x_662_);
v_declName_664_ = l_Lean_Expr_constName_x21(v_f_660_);
lean_dec_ref(v_f_660_);
lean_inc(v_declName_664_);
v___x_665_ = l_Lean_Meta_isCoeDecl(v_env_663_, v_declName_664_);
if (v___x_665_ == 0)
{
lean_dec(v_declName_664_);
lean_dec_ref(v_e_648_);
v___y_656_ = v___y_649_;
goto v___jp_655_;
}
else
{
lean_object* v___x_666_; 
lean_inc(v_declName_664_);
lean_inc_ref(v_e_648_);
v___x_666_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_648_, v_declName_664_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; uint8_t v___x_668_; lean_object* v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = 0;
v___x_669_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_667_, v___x_668_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_722_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v___x_669_);
v_snd_671_ = lean_ctor_get(v_a_670_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_a_670_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_a_670_, 0);
lean_dec(v_unused_723_);
v___x_673_ = v_a_670_;
v_isShared_674_ = v_isSharedCheck_722_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_dec(v_a_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_722_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; 
lean_inc_ref(v_e_648_);
v___x_675_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_648_, v___x_668_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_713_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_713_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_713_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_713_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_a_676_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_712_; 
v_val_680_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_712_ == 0)
{
v___x_682_ = v_a_676_;
v_isShared_683_ = v_isSharedCheck_712_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_a_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_712_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___y_685_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_697_ = lean_name_eq(v_declName_664_, v___x_696_);
lean_dec(v_declName_664_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_e_648_);
v___y_685_ = v_snd_671_;
goto v___jp_684_;
}
else
{
lean_object* v_dummy_698_; lean_object* v_nargs_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_dummy_698_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_699_ = l_Lean_Expr_getAppNumArgs(v_e_648_);
lean_inc(v_nargs_699_);
v___x_700_ = lean_mk_array(v_nargs_699_, v_dummy_698_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_sub(v_nargs_699_, v___x_701_);
lean_dec(v_nargs_699_);
v___x_703_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_648_, v___x_700_, v___x_702_);
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_array_get_size(v___x_703_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec_ref(v___x_703_);
v___y_685_ = v_snd_671_;
goto v___jp_684_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_array_fget(v___x_703_, v___x_704_);
lean_dec_ref(v___x_703_);
v___x_708_ = l_Lean_Expr_getAppFn(v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = l_Lean_Expr_isConst(v___x_708_);
if (v___x_709_ == 0)
{
lean_dec_ref(v___x_708_);
v___y_685_ = v_snd_671_;
goto v___jp_684_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_Expr_constName_x21(v___x_708_);
lean_dec_ref(v___x_708_);
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_snd_671_);
v___y_685_ = v___x_711_;
goto v___jp_684_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_Expr_headBeta(v_val_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_686_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_695_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___y_685_);
lean_ctor_set(v___x_673_, 0, v___x_688_);
v___x_690_ = v___x_673_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___y_685_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_690_);
v___x_692_ = v___x_678_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_678_);
lean_dec(v_a_676_);
lean_del_object(v___x_673_);
lean_dec(v_declName_664_);
lean_dec_ref(v_e_648_);
v___y_656_ = v_snd_671_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_673_);
lean_dec(v_snd_671_);
lean_dec(v_declName_664_);
lean_dec_ref(v_e_648_);
v_a_714_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_675_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_675_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_declName_664_);
lean_dec_ref(v_e_648_);
v_a_724_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_669_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_669_);
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
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_declName_664_);
lean_dec(v___y_649_);
lean_dec_ref(v_e_648_);
v_a_732_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_666_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_666_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___y_656_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_expandCoe___lam__1(v_e_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_749_);
v___x_757_ = lean_apply_8(v_k_748_, v_b_751_, v___y_749_, v___y_750_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, lean_box(0));
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_758_, v___y_759_, v___y_760_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_759_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_768_, uint8_t v_bi_769_, lean_object* v_type_770_, lean_object* v_k_771_, uint8_t v_kind_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; 
lean_inc(v___y_773_);
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_780_, 0, v_k_771_);
lean_closure_set(v___f_780_, 1, v___y_773_);
lean_closure_set(v___f_780_, 2, v___y_774_);
v___x_781_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_768_, v_bi_769_, v_type_770_, v___f_780_, v_kind_772_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
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
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_798_, lean_object* v_bi_799_, lean_object* v_type_800_, lean_object* v_k_801_, lean_object* v_kind_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_bi_boxed_810_; uint8_t v_kind_boxed_811_; lean_object* v_res_812_; 
v_bi_boxed_810_ = lean_unbox(v_bi_799_);
v_kind_boxed_811_ = lean_unbox(v_kind_802_);
v_res_812_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_798_, v_bi_boxed_810_, v_type_800_, v_k_801_, v_kind_boxed_811_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_813_);
lean_ctor_set(v___x_820_, 1, v___y_814_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_830_, lean_object* v_type_831_, lean_object* v_val_832_, lean_object* v_k_833_, uint8_t v_nondep_834_, uint8_t v_kind_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___f_843_; lean_object* v___x_844_; 
lean_inc(v___y_836_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_843_, 0, v_k_833_);
lean_closure_set(v___f_843_, 1, v___y_836_);
lean_closure_set(v___f_843_, 2, v___y_837_);
v___x_844_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_830_, v_type_831_, v_val_832_, v___f_843_, v_nondep_834_, v_kind_835_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
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
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_861_, lean_object* v_type_862_, lean_object* v_val_863_, lean_object* v_k_864_, lean_object* v_nondep_865_, lean_object* v_kind_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_nondep_boxed_874_; uint8_t v_kind_boxed_875_; lean_object* v_res_876_; 
v_nondep_boxed_874_ = lean_unbox(v_nondep_865_);
v_kind_boxed_875_ = lean_unbox(v_kind_866_);
v_res_876_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_861_, v_type_862_, v_val_863_, v_k_864_, v_nondep_boxed_874_, v_kind_boxed_875_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_867_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_877_, lean_object* v_b_878_, lean_object* v_x_879_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
lean_dec(v_b_878_);
lean_dec_ref(v_a_877_);
return v_x_879_;
}
else
{
lean_object* v_key_880_; lean_object* v_value_881_; lean_object* v_tail_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v_key_880_ = lean_ctor_get(v_x_879_, 0);
v_value_881_ = lean_ctor_get(v_x_879_, 1);
v_tail_882_ = lean_ctor_get(v_x_879_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_879_);
if (v_isSharedCheck_894_ == 0)
{
v___x_884_ = v_x_879_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_tail_882_);
lean_inc(v_value_881_);
lean_inc(v_key_880_);
lean_dec(v_x_879_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
uint8_t v___x_886_; 
v___x_886_ = l_Lean_ExprStructEq_beq(v_key_880_, v_a_877_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_877_, v_b_878_, v_tail_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 2, v___x_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_key_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_value_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_value_881_);
lean_dec(v_key_880_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v_b_878_);
lean_ctor_set(v___x_884_, 0, v_a_877_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_b_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_tail_882_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
else
{
lean_object* v_key_898_; lean_object* v_tail_899_; uint8_t v___x_900_; 
v_key_898_ = lean_ctor_get(v_x_896_, 0);
v_tail_899_ = lean_ctor_get(v_x_896_, 2);
v___x_900_ = l_Lean_ExprStructEq_beq(v_key_898_, v_a_895_);
if (v___x_900_ == 0)
{
v_x_896_ = v_tail_899_;
goto _start;
}
else
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec_ref(v_a_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
return v_x_906_;
}
else
{
lean_object* v_key_908_; lean_object* v_value_909_; lean_object* v_tail_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_933_; 
v_key_908_ = lean_ctor_get(v_x_907_, 0);
v_value_909_ = lean_ctor_get(v_x_907_, 1);
v_tail_910_ = lean_ctor_get(v_x_907_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_933_ == 0)
{
v___x_912_ = v_x_907_;
v_isShared_913_ = v_isSharedCheck_933_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_tail_910_);
lean_inc(v_value_909_);
lean_inc(v_key_908_);
lean_dec(v_x_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_933_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v_fold_918_; uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_914_ = lean_array_get_size(v_x_906_);
v___x_915_ = l_Lean_ExprStructEq_hash(v_key_908_);
v___x_916_ = 32ULL;
v___x_917_ = lean_uint64_shift_right(v___x_915_, v___x_916_);
v_fold_918_ = lean_uint64_xor(v___x_915_, v___x_917_);
v___x_919_ = 16ULL;
v___x_920_ = lean_uint64_shift_right(v_fold_918_, v___x_919_);
v___x_921_ = lean_uint64_xor(v_fold_918_, v___x_920_);
v___x_922_ = lean_uint64_to_usize(v___x_921_);
v___x_923_ = lean_usize_of_nat(v___x_914_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_sub(v___x_923_, v___x_924_);
v___x_926_ = lean_usize_land(v___x_922_, v___x_925_);
v___x_927_ = lean_array_uget_borrowed(v_x_906_, v___x_926_);
lean_inc(v___x_927_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 2, v___x_927_);
v___x_929_ = v___x_912_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_key_908_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_value_909_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v___x_927_);
v___x_929_ = v_reuseFailAlloc_932_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_array_uset(v_x_906_, v___x_926_, v___x_929_);
v_x_906_ = v___x_930_;
v_x_907_ = v_tail_910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_934_, lean_object* v_source_935_, lean_object* v_target_936_){
_start:
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_array_get_size(v_source_935_);
v___x_938_ = lean_nat_dec_lt(v_i_934_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_source_935_);
lean_dec(v_i_934_);
return v_target_936_;
}
else
{
lean_object* v_es_939_; lean_object* v___x_940_; lean_object* v_source_941_; lean_object* v_target_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_es_939_ = lean_array_fget(v_source_935_, v_i_934_);
v___x_940_ = lean_box(0);
v_source_941_ = lean_array_fset(v_source_935_, v_i_934_, v___x_940_);
v_target_942_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_936_, v_es_939_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_i_934_, v___x_943_);
lean_dec(v_i_934_);
v_i_934_ = v___x_944_;
v_source_935_ = v_source_941_;
v_target_936_ = v_target_942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_nbuckets_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_947_ = lean_array_get_size(v_data_946_);
v___x_948_ = lean_unsigned_to_nat(2u);
v_nbuckets_949_ = lean_nat_mul(v___x_947_, v___x_948_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_box(0);
v___x_952_ = lean_mk_array(v_nbuckets_949_, v___x_951_);
v___x_953_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_950_, v_data_946_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_954_, lean_object* v_a_955_, lean_object* v_b_956_){
_start:
{
lean_object* v_size_957_; lean_object* v_buckets_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1001_; 
v_size_957_ = lean_ctor_get(v_m_954_, 0);
v_buckets_958_ = lean_ctor_get(v_m_954_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_m_954_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_960_ = v_m_954_;
v_isShared_961_ = v_isSharedCheck_1001_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_buckets_958_);
lean_inc(v_size_957_);
lean_dec(v_m_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1001_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v_fold_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; lean_object* v_bkt_975_; uint8_t v___x_976_; 
v___x_962_ = lean_array_get_size(v_buckets_958_);
v___x_963_ = l_Lean_ExprStructEq_hash(v_a_955_);
v___x_964_ = 32ULL;
v___x_965_ = lean_uint64_shift_right(v___x_963_, v___x_964_);
v_fold_966_ = lean_uint64_xor(v___x_963_, v___x_965_);
v___x_967_ = 16ULL;
v___x_968_ = lean_uint64_shift_right(v_fold_966_, v___x_967_);
v___x_969_ = lean_uint64_xor(v_fold_966_, v___x_968_);
v___x_970_ = lean_uint64_to_usize(v___x_969_);
v___x_971_ = lean_usize_of_nat(v___x_962_);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_sub(v___x_971_, v___x_972_);
v___x_974_ = lean_usize_land(v___x_970_, v___x_973_);
v_bkt_975_ = lean_array_uget_borrowed(v_buckets_958_, v___x_974_);
v___x_976_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_955_, v_bkt_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v_size_x27_978_; lean_object* v___x_979_; lean_object* v_buckets_x27_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v_size_x27_978_ = lean_nat_add(v_size_957_, v___x_977_);
lean_dec(v_size_957_);
lean_inc(v_bkt_975_);
v___x_979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_979_, 0, v_a_955_);
lean_ctor_set(v___x_979_, 1, v_b_956_);
lean_ctor_set(v___x_979_, 2, v_bkt_975_);
v_buckets_x27_980_ = lean_array_uset(v_buckets_958_, v___x_974_, v___x_979_);
v___x_981_ = lean_unsigned_to_nat(4u);
v___x_982_ = lean_nat_mul(v_size_x27_978_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(3u);
v___x_984_ = lean_nat_div(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_array_get_size(v_buckets_x27_980_);
v___x_986_ = lean_nat_dec_le(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v_val_987_; lean_object* v___x_989_; 
v_val_987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_980_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_val_987_);
lean_ctor_set(v___x_960_, 0, v_size_x27_978_);
v___x_989_ = v___x_960_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_x27_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_val_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_object* v___x_992_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_buckets_x27_980_);
lean_ctor_set(v___x_960_, 0, v_size_x27_978_);
v___x_992_ = v___x_960_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_size_x27_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_buckets_x27_980_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v___x_994_; lean_object* v_buckets_x27_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc(v_bkt_975_);
v___x_994_ = lean_box(0);
v_buckets_x27_995_ = lean_array_uset(v_buckets_958_, v___x_974_, v___x_994_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_955_, v_b_956_, v_bkt_975_);
v___x_997_ = lean_array_uset(v_buckets_x27_995_, v___x_974_, v___x_996_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_997_);
v___x_999_ = v___x_960_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_size_957_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1002_, lean_object* v_e_1003_, lean_object* v_fst_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = lean_st_ref_take(v_a_1002_);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1006_, v_e_1003_, v_fst_1004_);
v___x_1008_ = lean_st_ref_set(v_a_1002_, v___x_1007_);
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1010_, lean_object* v_e_1011_, lean_object* v_fst_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1010_, v_e_1011_, v_fst_1012_);
lean_dec(v_a_1010_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l_Lean_maxRecDepthErrorMessage;
v___x_1021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1023_ = l_Lean_MessageData_ofFormat(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1025_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1026_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_ref_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___y_1044_; lean_object* v_fileName_1061_; lean_object* v_fileMap_1062_; lean_object* v_options_1063_; lean_object* v_currRecDepth_1064_; lean_object* v_maxRecDepth_1065_; lean_object* v_ref_1066_; lean_object* v_currNamespace_1067_; lean_object* v_openDecls_1068_; lean_object* v_initHeartbeats_1069_; lean_object* v_maxHeartbeats_1070_; lean_object* v_quotContext_1071_; lean_object* v_currMacroScope_1072_; uint8_t v_diag_1073_; lean_object* v_cancelTk_x3f_1074_; uint8_t v_suppressElabErrors_1075_; lean_object* v_inheritedTraceOptions_1076_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_fileName_1061_ = lean_ctor_get(v___y_1040_, 0);
v_fileMap_1062_ = lean_ctor_get(v___y_1040_, 1);
v_options_1063_ = lean_ctor_get(v___y_1040_, 2);
v_currRecDepth_1064_ = lean_ctor_get(v___y_1040_, 3);
v_maxRecDepth_1065_ = lean_ctor_get(v___y_1040_, 4);
v_ref_1066_ = lean_ctor_get(v___y_1040_, 5);
v_currNamespace_1067_ = lean_ctor_get(v___y_1040_, 6);
v_openDecls_1068_ = lean_ctor_get(v___y_1040_, 7);
v_initHeartbeats_1069_ = lean_ctor_get(v___y_1040_, 8);
v_maxHeartbeats_1070_ = lean_ctor_get(v___y_1040_, 9);
v_quotContext_1071_ = lean_ctor_get(v___y_1040_, 10);
v_currMacroScope_1072_ = lean_ctor_get(v___y_1040_, 11);
v_diag_1073_ = lean_ctor_get_uint8(v___y_1040_, sizeof(void*)*14);
v_cancelTk_x3f_1074_ = lean_ctor_get(v___y_1040_, 12);
v_suppressElabErrors_1075_ = lean_ctor_get_uint8(v___y_1040_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1076_ = lean_ctor_get(v___y_1040_, 13);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_nat_dec_eq(v_maxRecDepth_1065_, v___x_1082_);
if (v___x_1083_ == 0)
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_currRecDepth_1064_, v_maxRecDepth_1065_);
if (v___x_1084_ == 0)
{
goto v___jp_1077_;
}
else
{
lean_object* v___x_1085_; 
lean_dec(v___y_1037_);
lean_dec_ref(v_x_1035_);
lean_inc(v_ref_1066_);
v___x_1085_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1066_);
v___y_1044_ = v___x_1085_;
goto v___jp_1043_;
}
}
else
{
goto v___jp_1077_;
}
v___jp_1043_:
{
if (lean_obj_tag(v___y_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___y_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___y_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___y_1044_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___y_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___y_1044_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___y_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
v___jp_1077_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_currRecDepth_1064_, v___x_1078_);
lean_inc_ref(v_inheritedTraceOptions_1076_);
lean_inc(v_cancelTk_x3f_1074_);
lean_inc(v_currMacroScope_1072_);
lean_inc(v_quotContext_1071_);
lean_inc(v_maxHeartbeats_1070_);
lean_inc(v_initHeartbeats_1069_);
lean_inc(v_openDecls_1068_);
lean_inc(v_currNamespace_1067_);
lean_inc(v_ref_1066_);
lean_inc(v_maxRecDepth_1065_);
lean_inc_ref(v_options_1063_);
lean_inc_ref(v_fileMap_1062_);
lean_inc_ref(v_fileName_1061_);
v___x_1080_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1080_, 0, v_fileName_1061_);
lean_ctor_set(v___x_1080_, 1, v_fileMap_1062_);
lean_ctor_set(v___x_1080_, 2, v_options_1063_);
lean_ctor_set(v___x_1080_, 3, v___x_1079_);
lean_ctor_set(v___x_1080_, 4, v_maxRecDepth_1065_);
lean_ctor_set(v___x_1080_, 5, v_ref_1066_);
lean_ctor_set(v___x_1080_, 6, v_currNamespace_1067_);
lean_ctor_set(v___x_1080_, 7, v_openDecls_1068_);
lean_ctor_set(v___x_1080_, 8, v_initHeartbeats_1069_);
lean_ctor_set(v___x_1080_, 9, v_maxHeartbeats_1070_);
lean_ctor_set(v___x_1080_, 10, v_quotContext_1071_);
lean_ctor_set(v___x_1080_, 11, v_currMacroScope_1072_);
lean_ctor_set(v___x_1080_, 12, v_cancelTk_x3f_1074_);
lean_ctor_set(v___x_1080_, 13, v_inheritedTraceOptions_1076_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*14, v_diag_1073_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*14 + 1, v_suppressElabErrors_1075_);
lean_inc(v___y_1041_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1036_);
v___x_1081_ = lean_apply_7(v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___x_1080_, v___y_1041_, lean_box(0));
v___y_1044_ = v___x_1081_;
goto v___jp_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1087_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
else
{
lean_object* v_key_1098_; lean_object* v_value_1099_; lean_object* v_tail_1100_; uint8_t v___x_1101_; 
v_key_1098_ = lean_ctor_get(v_x_1096_, 0);
v_value_1099_ = lean_ctor_get(v_x_1096_, 1);
v_tail_1100_ = lean_ctor_get(v_x_1096_, 2);
v___x_1101_ = l_Lean_ExprStructEq_beq(v_key_1098_, v_a_1095_);
if (v___x_1101_ == 0)
{
v_x_1096_ = v_tail_1100_;
goto _start;
}
else
{
lean_object* v___x_1103_; 
lean_inc(v_value_1099_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_value_1099_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1104_, v_x_1105_);
lean_dec(v_x_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_buckets_1109_; lean_object* v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v_fold_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_buckets_1109_ = lean_ctor_get(v_m_1107_, 1);
v___x_1110_ = lean_array_get_size(v_buckets_1109_);
v___x_1111_ = l_Lean_ExprStructEq_hash(v_a_1108_);
v___x_1112_ = 32ULL;
v___x_1113_ = lean_uint64_shift_right(v___x_1111_, v___x_1112_);
v_fold_1114_ = lean_uint64_xor(v___x_1111_, v___x_1113_);
v___x_1115_ = 16ULL;
v___x_1116_ = lean_uint64_shift_right(v_fold_1114_, v___x_1115_);
v___x_1117_ = lean_uint64_xor(v_fold_1114_, v___x_1116_);
v___x_1118_ = lean_uint64_to_usize(v___x_1117_);
v___x_1119_ = lean_usize_of_nat(v___x_1110_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_sub(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_usize_land(v___x_1118_, v___x_1121_);
v___x_1123_ = lean_array_uget_borrowed(v_buckets_1109_, v___x_1122_);
v___x_1124_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1108_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1125_, v_a_1126_);
lean_dec_ref(v_a_1126_);
lean_dec_ref(v_m_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_apply_1(v_x_1129_, lean_box(0));
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_1130_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1139_, v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1151_, lean_object* v_pre_1152_, lean_object* v_post_1153_, uint8_t v_usedLetOnly_1154_, uint8_t v_skipConstInApp_1155_, uint8_t v_skipInstances_1156_, lean_object* v_body_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_array_push(v_fvars_1151_, v_x_1158_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1152_, v_post_1153_, v_usedLetOnly_1154_, v_skipConstInApp_1155_, v_skipInstances_1156_, v___x_1166_, v_body_1157_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1168_, lean_object* v_pre_1169_, lean_object* v_post_1170_, lean_object* v_usedLetOnly_1171_, lean_object* v_skipConstInApp_1172_, lean_object* v_skipInstances_1173_, lean_object* v_body_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_usedLetOnly_boxed_1183_; uint8_t v_skipConstInApp_boxed_1184_; uint8_t v_skipInstances_boxed_1185_; lean_object* v_res_1186_; 
v_usedLetOnly_boxed_1183_ = lean_unbox(v_usedLetOnly_1171_);
v_skipConstInApp_boxed_1184_ = lean_unbox(v_skipConstInApp_1172_);
v_skipInstances_boxed_1185_ = lean_unbox(v_skipInstances_1173_);
v_res_1186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1168_, v_pre_1169_, v_post_1170_, v_usedLetOnly_boxed_1183_, v_skipConstInApp_boxed_1184_, v_skipInstances_boxed_1185_, v_body_1174_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1176_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1187_, lean_object* v_post_1188_, uint8_t v_usedLetOnly_1189_, uint8_t v_skipConstInApp_1190_, uint8_t v_skipInstances_1191_, lean_object* v_e_1192_, lean_object* v_a_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
lean_inc_ref(v_post_1188_);
lean_inc(v___y_1198_);
lean_inc_ref(v___y_1197_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
lean_inc_ref(v_e_1192_);
v___x_1200_ = lean_apply_7(v_post_1188_, v_e_1192_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, lean_box(0));
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1232_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1232_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1232_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1231_; 
v_fst_1205_ = lean_ctor_get(v_a_1201_, 0);
v_snd_1206_ = lean_ctor_get(v_a_1201_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_a_1201_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1208_ = v_a_1201_;
v_isShared_1209_ = v_isSharedCheck_1231_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
lean_dec(v_a_1201_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1231_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___y_1211_; 
switch(lean_obj_tag(v_fst_1205_))
{
case 0:
{
lean_object* v_e_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1208_);
lean_del_object(v___x_1203_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_post_1188_);
lean_dec_ref(v_pre_1187_);
v_e_1218_ = lean_ctor_get(v_fst_1205_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_fst_1205_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v_fst_1205_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_e_1218_);
lean_dec(v_fst_1205_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_e_1218_);
lean_ctor_set(v___x_1222_, 1, v_snd_1206_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
case 1:
{
lean_object* v_e_1227_; lean_object* v___x_1228_; 
lean_del_object(v___x_1208_);
lean_del_object(v___x_1203_);
lean_dec_ref(v_e_1192_);
v_e_1227_ = lean_ctor_get(v_fst_1205_, 0);
lean_inc_ref(v_e_1227_);
lean_dec_ref(v_fst_1205_);
v___x_1228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1187_, v_post_1188_, v_usedLetOnly_1189_, v_skipConstInApp_1190_, v_skipInstances_1191_, v_e_1227_, v_a_1193_, v_snd_1206_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1228_;
}
default: 
{
lean_object* v_e_x3f_1229_; 
lean_dec_ref(v_post_1188_);
lean_dec_ref(v_pre_1187_);
v_e_x3f_1229_ = lean_ctor_get(v_fst_1205_, 0);
lean_inc(v_e_x3f_1229_);
lean_dec_ref(v_fst_1205_);
if (lean_obj_tag(v_e_x3f_1229_) == 0)
{
v___y_1211_ = v_e_1192_;
goto v___jp_1210_;
}
else
{
lean_object* v_val_1230_; 
lean_dec_ref(v_e_1192_);
v_val_1230_ = lean_ctor_get(v_e_x3f_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v_e_x3f_1229_);
v___y_1211_ = v_val_1230_;
goto v___jp_1210_;
}
}
}
v___jp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___y_1211_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___y_1211_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_snd_1206_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1213_);
v___x_1215_ = v___x_1203_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_post_1188_);
lean_dec_ref(v_pre_1187_);
v_a_1233_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1200_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1200_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1241_, lean_object* v_post_1242_, uint8_t v_usedLetOnly_1243_, uint8_t v_skipConstInApp_1244_, uint8_t v_skipInstances_1245_, lean_object* v_fvars_1246_, lean_object* v_e_1247_, lean_object* v_a_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
if (lean_obj_tag(v_e_1247_) == 6)
{
lean_object* v_binderName_1255_; lean_object* v_binderType_1256_; lean_object* v_body_1257_; uint8_t v_binderInfo_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_binderName_1255_ = lean_ctor_get(v_e_1247_, 0);
lean_inc(v_binderName_1255_);
v_binderType_1256_ = lean_ctor_get(v_e_1247_, 1);
lean_inc_ref(v_binderType_1256_);
v_body_1257_ = lean_ctor_get(v_e_1247_, 2);
lean_inc_ref(v_body_1257_);
v_binderInfo_1258_ = lean_ctor_get_uint8(v_e_1247_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1247_);
v___x_1259_ = lean_expr_instantiate_rev(v_binderType_1256_, v_fvars_1246_);
lean_dec_ref(v_binderType_1256_);
lean_inc_ref(v_post_1242_);
lean_inc_ref(v_pre_1241_);
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1241_, v_post_1242_, v_usedLetOnly_1243_, v_skipConstInApp_1244_, v_skipInstances_1245_, v___x_1259_, v_a_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v_fst_1262_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v_a_1261_, 1);
lean_inc(v_snd_1263_);
lean_dec(v_a_1261_);
v___x_1264_ = lean_box(v_usedLetOnly_1243_);
v___x_1265_ = lean_box(v_skipConstInApp_1244_);
v___x_1266_ = lean_box(v_skipInstances_1245_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1267_, 0, v_fvars_1246_);
lean_closure_set(v___f_1267_, 1, v_pre_1241_);
lean_closure_set(v___f_1267_, 2, v_post_1242_);
lean_closure_set(v___f_1267_, 3, v___x_1264_);
lean_closure_set(v___f_1267_, 4, v___x_1265_);
lean_closure_set(v___f_1267_, 5, v___x_1266_);
lean_closure_set(v___f_1267_, 6, v_body_1257_);
v___x_1268_ = 0;
v___x_1269_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1255_, v_binderInfo_1258_, v_fst_1262_, v___f_1267_, v___x_1268_, v_a_1248_, v_snd_1263_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1269_;
}
else
{
lean_dec_ref(v_body_1257_);
lean_dec(v_binderName_1255_);
lean_dec_ref(v_fvars_1246_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_expr_instantiate_rev(v_e_1247_, v_fvars_1246_);
lean_dec_ref(v_e_1247_);
lean_inc_ref(v_post_1242_);
lean_inc_ref(v_pre_1241_);
v___x_1271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1241_, v_post_1242_, v_usedLetOnly_1243_, v_skipConstInApp_1244_, v_skipInstances_1245_, v___x_1270_, v_a_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; uint8_t v___x_1275_; uint8_t v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v_fst_1273_ = lean_ctor_get(v_a_1272_, 0);
lean_inc(v_fst_1273_);
v_snd_1274_ = lean_ctor_get(v_a_1272_, 1);
lean_inc(v_snd_1274_);
lean_dec(v_a_1272_);
v___x_1275_ = 0;
v___x_1276_ = 1;
v___x_1277_ = 1;
v___x_1278_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1246_, v_fst_1273_, v___x_1275_, v_usedLetOnly_1243_, v___x_1275_, v___x_1276_, v___x_1277_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec_ref(v_fvars_1246_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1241_, v_post_1242_, v_usedLetOnly_1243_, v_skipConstInApp_1244_, v_skipInstances_1245_, v_a_1279_, v_a_1248_, v_snd_1274_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_snd_1274_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
v_a_1281_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1278_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1278_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1246_);
lean_dec_ref(v_post_1242_);
lean_dec_ref(v_pre_1241_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1289_, lean_object* v_pre_1290_, lean_object* v_post_1291_, uint8_t v_usedLetOnly_1292_, uint8_t v_skipConstInApp_1293_, uint8_t v_skipInstances_1294_, lean_object* v_body_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_array_push(v_fvars_1289_, v_x_1296_);
v___x_1305_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1290_, v_post_1291_, v_usedLetOnly_1292_, v_skipConstInApp_1293_, v_skipInstances_1294_, v___x_1304_, v_body_1295_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1306_, lean_object* v_pre_1307_, lean_object* v_post_1308_, lean_object* v_usedLetOnly_1309_, lean_object* v_skipConstInApp_1310_, lean_object* v_skipInstances_1311_, lean_object* v_body_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_usedLetOnly_boxed_1321_; uint8_t v_skipConstInApp_boxed_1322_; uint8_t v_skipInstances_boxed_1323_; lean_object* v_res_1324_; 
v_usedLetOnly_boxed_1321_ = lean_unbox(v_usedLetOnly_1309_);
v_skipConstInApp_boxed_1322_ = lean_unbox(v_skipConstInApp_1310_);
v_skipInstances_boxed_1323_ = lean_unbox(v_skipInstances_1311_);
v_res_1324_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1306_, v_pre_1307_, v_post_1308_, v_usedLetOnly_boxed_1321_, v_skipConstInApp_boxed_1322_, v_skipInstances_boxed_1323_, v_body_1312_, v_x_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1314_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1325_, lean_object* v_post_1326_, uint8_t v_usedLetOnly_1327_, uint8_t v_skipConstInApp_1328_, uint8_t v_skipInstances_1329_, lean_object* v_fvars_1330_, lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
if (lean_obj_tag(v_e_1331_) == 8)
{
lean_object* v_declName_1339_; lean_object* v_type_1340_; lean_object* v_value_1341_; lean_object* v_body_1342_; uint8_t v_nondep_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_declName_1339_ = lean_ctor_get(v_e_1331_, 0);
lean_inc(v_declName_1339_);
v_type_1340_ = lean_ctor_get(v_e_1331_, 1);
lean_inc_ref(v_type_1340_);
v_value_1341_ = lean_ctor_get(v_e_1331_, 2);
lean_inc_ref(v_value_1341_);
v_body_1342_ = lean_ctor_get(v_e_1331_, 3);
lean_inc_ref(v_body_1342_);
v_nondep_1343_ = lean_ctor_get_uint8(v_e_1331_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1331_);
v___x_1344_ = lean_expr_instantiate_rev(v_type_1340_, v_fvars_1330_);
lean_dec_ref(v_type_1340_);
lean_inc_ref(v_post_1326_);
lean_inc_ref(v_pre_1325_);
v___x_1345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1325_, v_post_1326_, v_usedLetOnly_1327_, v_skipConstInApp_1328_, v_skipInstances_1329_, v___x_1344_, v_a_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
v_fst_1347_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_fst_1347_);
v_snd_1348_ = lean_ctor_get(v_a_1346_, 1);
lean_inc(v_snd_1348_);
lean_dec(v_a_1346_);
v___x_1349_ = lean_expr_instantiate_rev(v_value_1341_, v_fvars_1330_);
lean_dec_ref(v_value_1341_);
lean_inc_ref(v_post_1326_);
lean_inc_ref(v_pre_1325_);
v___x_1350_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1325_, v_post_1326_, v_usedLetOnly_1327_, v_skipConstInApp_1328_, v_skipInstances_1329_, v___x_1349_, v_a_1332_, v_snd_1348_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v_fst_1352_ = lean_ctor_get(v_a_1351_, 0);
lean_inc(v_fst_1352_);
v_snd_1353_ = lean_ctor_get(v_a_1351_, 1);
lean_inc(v_snd_1353_);
lean_dec(v_a_1351_);
v___x_1354_ = lean_box(v_usedLetOnly_1327_);
v___x_1355_ = lean_box(v_skipConstInApp_1328_);
v___x_1356_ = lean_box(v_skipInstances_1329_);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1357_, 0, v_fvars_1330_);
lean_closure_set(v___f_1357_, 1, v_pre_1325_);
lean_closure_set(v___f_1357_, 2, v_post_1326_);
lean_closure_set(v___f_1357_, 3, v___x_1354_);
lean_closure_set(v___f_1357_, 4, v___x_1355_);
lean_closure_set(v___f_1357_, 5, v___x_1356_);
lean_closure_set(v___f_1357_, 6, v_body_1342_);
v___x_1358_ = 0;
v___x_1359_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1339_, v_fst_1347_, v_fst_1352_, v___f_1357_, v_nondep_1343_, v___x_1358_, v_a_1332_, v_snd_1353_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1359_;
}
else
{
lean_dec(v_fst_1347_);
lean_dec_ref(v_body_1342_);
lean_dec(v_declName_1339_);
lean_dec_ref(v_fvars_1330_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
return v___x_1350_;
}
}
else
{
lean_dec_ref(v_body_1342_);
lean_dec_ref(v_value_1341_);
lean_dec(v_declName_1339_);
lean_dec_ref(v_fvars_1330_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
return v___x_1345_;
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_expr_instantiate_rev(v_e_1331_, v_fvars_1330_);
lean_dec_ref(v_e_1331_);
lean_inc_ref(v_post_1326_);
lean_inc_ref(v_pre_1325_);
v___x_1361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1325_, v_post_1326_, v_usedLetOnly_1327_, v_skipConstInApp_1328_, v_skipInstances_1329_, v___x_1360_, v_a_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; uint8_t v___x_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v_fst_1363_ = lean_ctor_get(v_a_1362_, 0);
lean_inc(v_fst_1363_);
v_snd_1364_ = lean_ctor_get(v_a_1362_, 1);
lean_inc(v_snd_1364_);
lean_dec(v_a_1362_);
v___x_1365_ = 0;
v___x_1366_ = 1;
v___x_1367_ = l_Lean_Meta_mkLetFVars(v_fvars_1330_, v_fst_1363_, v_usedLetOnly_1327_, v___x_1365_, v___x_1366_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec_ref(v_fvars_1330_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1325_, v_post_1326_, v_usedLetOnly_1327_, v_skipConstInApp_1328_, v_skipInstances_1329_, v_a_1368_, v_a_1332_, v_snd_1364_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1369_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_snd_1364_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
v_a_1370_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1367_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1367_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1330_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1378_, lean_object* v_post_1379_, uint8_t v_usedLetOnly_1380_, uint8_t v_skipConstInApp_1381_, uint8_t v_skipInstances_1382_, size_t v_sz_1383_, size_t v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_lt(v_i_1384_, v_sz_1383_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_post_1379_);
lean_dec_ref(v_pre_1378_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_bs_1385_);
lean_ctor_set(v___x_1394_, 1, v___y_1387_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
else
{
lean_object* v_v_1396_; lean_object* v___x_1397_; 
v_v_1396_ = lean_array_uget_borrowed(v_bs_1385_, v_i_1384_);
lean_inc(v_v_1396_);
lean_inc_ref(v_post_1379_);
lean_inc_ref(v_pre_1378_);
v___x_1397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1378_, v_post_1379_, v_usedLetOnly_1380_, v_skipConstInApp_1381_, v_skipInstances_1382_, v_v_1396_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1401_; lean_object* v_bs_x27_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
v_fst_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v_a_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec(v_a_1398_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v_bs_x27_1402_ = lean_array_uset(v_bs_1385_, v_i_1384_, v___x_1401_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1384_, v___x_1403_);
v___x_1405_ = lean_array_uset(v_bs_x27_1402_, v_i_1384_, v_fst_1399_);
v_i_1384_ = v___x_1404_;
v_bs_1385_ = v___x_1405_;
v___y_1387_ = v_snd_1400_;
goto _start;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_bs_1385_);
lean_dec_ref(v_post_1379_);
lean_dec_ref(v_pre_1378_);
v_a_1407_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1397_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1415_, lean_object* v_post_1416_, uint8_t v_usedLetOnly_1417_, uint8_t v_skipConstInApp_1418_, uint8_t v_skipInstances_1419_, lean_object* v___x_1420_, lean_object* v___y_1421_, lean_object* v_b_1422_, lean_object* v_a_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1415_, v_post_1416_, v_usedLetOnly_1417_, v_skipConstInApp_1418_, v_skipInstances_1419_, v___x_1420_, v___y_1421_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1449_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1449_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1449_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_fst_1435_; lean_object* v_snd_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1448_; 
v_fst_1435_ = lean_ctor_get(v_a_1431_, 0);
v_snd_1436_ = lean_ctor_get(v_a_1431_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1438_ = v_a_1431_;
v_isShared_1439_ = v_isSharedCheck_1448_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_snd_1436_);
lean_inc(v_fst_1435_);
lean_dec(v_a_1431_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1448_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = lean_array_fset(v_b_1422_, v_a_1423_, v_fst_1435_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1436_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1443_);
v___x_1445_ = v___x_1433_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_b_1422_);
v_a_1450_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1430_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1430_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1458_, lean_object* v_post_1459_, lean_object* v_usedLetOnly_1460_, lean_object* v_skipConstInApp_1461_, lean_object* v_skipInstances_1462_, lean_object* v___x_1463_, lean_object* v___y_1464_, lean_object* v_b_1465_, lean_object* v_a_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_usedLetOnly_boxed_1473_; uint8_t v_skipConstInApp_boxed_1474_; uint8_t v_skipInstances_boxed_1475_; lean_object* v_res_1476_; 
v_usedLetOnly_boxed_1473_ = lean_unbox(v_usedLetOnly_1460_);
v_skipConstInApp_boxed_1474_ = lean_unbox(v_skipConstInApp_1461_);
v_skipInstances_boxed_1475_ = lean_unbox(v_skipInstances_1462_);
v_res_1476_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1458_, v_post_1459_, v_usedLetOnly_boxed_1473_, v_skipConstInApp_boxed_1474_, v_skipInstances_boxed_1475_, v___x_1463_, v___y_1464_, v_b_1465_, v_a_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_a_1466_);
lean_dec(v___y_1464_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1477_, lean_object* v___x_1478_, lean_object* v_pre_1479_, lean_object* v_post_1480_, uint8_t v_usedLetOnly_1481_, uint8_t v_skipConstInApp_1482_, uint8_t v_skipInstances_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___y_1494_; uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v_a_1484_, v_upperBound_1477_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_post_1480_);
lean_dec_ref(v_pre_1479_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1485_);
lean_ctor_set(v___x_1529_, 1, v___y_1487_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1531_ = lean_array_fget_borrowed(v_b_1485_, v_a_1484_);
v___x_1532_ = lean_array_get_size(v___x_1478_);
v___x_1533_ = lean_nat_dec_lt(v_a_1484_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; 
lean_inc(v___x_1531_);
v___x_1534_ = lean_box(v_usedLetOnly_1481_);
v___x_1535_ = lean_box(v_skipConstInApp_1482_);
v___x_1536_ = lean_box(v_skipInstances_1483_);
lean_inc(v_a_1484_);
lean_inc(v___y_1486_);
lean_inc_ref(v_post_1480_);
lean_inc_ref(v_pre_1479_);
v___f_1537_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1537_, 0, v_pre_1479_);
lean_closure_set(v___f_1537_, 1, v_post_1480_);
lean_closure_set(v___f_1537_, 2, v___x_1534_);
lean_closure_set(v___f_1537_, 3, v___x_1535_);
lean_closure_set(v___f_1537_, 4, v___x_1536_);
lean_closure_set(v___f_1537_, 5, v___x_1531_);
lean_closure_set(v___f_1537_, 6, v___y_1486_);
lean_closure_set(v___f_1537_, 7, v_b_1485_);
lean_closure_set(v___f_1537_, 8, v_a_1484_);
v___y_1494_ = v___f_1537_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1538_; uint8_t v_isInstance_1539_; 
v___x_1538_ = lean_array_fget_borrowed(v___x_1478_, v_a_1484_);
v_isInstance_1539_ = lean_ctor_get_uint8(v___x_1538_, sizeof(void*)*1 + 4);
if (v_isInstance_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; 
lean_inc(v___x_1531_);
v___x_1540_ = lean_box(v_usedLetOnly_1481_);
v___x_1541_ = lean_box(v_skipConstInApp_1482_);
v___x_1542_ = lean_box(v_skipInstances_1483_);
lean_inc(v_a_1484_);
lean_inc(v___y_1486_);
lean_inc_ref(v_post_1480_);
lean_inc_ref(v_pre_1479_);
v___f_1543_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1543_, 0, v_pre_1479_);
lean_closure_set(v___f_1543_, 1, v_post_1480_);
lean_closure_set(v___f_1543_, 2, v___x_1540_);
lean_closure_set(v___f_1543_, 3, v___x_1541_);
lean_closure_set(v___f_1543_, 4, v___x_1542_);
lean_closure_set(v___f_1543_, 5, v___x_1531_);
lean_closure_set(v___f_1543_, 6, v___y_1486_);
lean_closure_set(v___f_1543_, 7, v_b_1485_);
lean_closure_set(v___f_1543_, 8, v_a_1484_);
v___y_1494_ = v___f_1543_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1544_; lean_object* v___f_1545_; 
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_b_1485_);
v___f_1545_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1545_, 0, v___x_1544_);
v___y_1494_ = v___f_1545_;
goto v___jp_1493_;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1495_; 
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
v___x_1495_ = lean_apply_6(v___y_1494_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, lean_box(0));
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1519_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1519_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_fst_1500_; 
v_fst_1500_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_fst_1500_);
if (lean_obj_tag(v_fst_1500_) == 0)
{
lean_object* v_snd_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_post_1480_);
lean_dec_ref(v_pre_1479_);
v_snd_1501_ = lean_ctor_get(v_a_1496_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_a_1496_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_a_1496_, 0);
lean_dec(v_unused_1513_);
v___x_1503_ = v_a_1496_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1501_);
lean_dec(v_a_1496_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_a_1505_; lean_object* v___x_1507_; 
v_a_1505_ = lean_ctor_get(v_fst_1500_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v_fst_1500_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v_a_1505_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_snd_1501_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1507_);
v___x_1509_ = v___x_1498_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_snd_1514_; lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_del_object(v___x_1498_);
v_snd_1514_ = lean_ctor_get(v_a_1496_, 1);
lean_inc(v_snd_1514_);
lean_dec(v_a_1496_);
v_a_1515_ = lean_ctor_get(v_fst_1500_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v_fst_1500_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_a_1484_, v___x_1516_);
lean_dec(v_a_1484_);
v_a_1484_ = v___x_1517_;
v_b_1485_ = v_a_1515_;
v___y_1487_ = v_snd_1514_;
goto _start;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_post_1480_);
lean_dec_ref(v_pre_1479_);
v_a_1520_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1495_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1495_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1546_, lean_object* v_pre_1547_, lean_object* v_post_1548_, uint8_t v_usedLetOnly_1549_, uint8_t v_skipConstInApp_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_f_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; 
if (lean_obj_tag(v_x_1551_) == 5)
{
lean_object* v_fn_1617_; lean_object* v_arg_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_fn_1617_ = lean_ctor_get(v_x_1551_, 0);
lean_inc_ref(v_fn_1617_);
v_arg_1618_ = lean_ctor_get(v_x_1551_, 1);
lean_inc_ref(v_arg_1618_);
lean_dec_ref(v_x_1551_);
v___x_1619_ = lean_array_set(v_x_1552_, v_x_1553_, v_arg_1618_);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_sub(v_x_1553_, v___x_1620_);
lean_dec(v_x_1553_);
v_x_1551_ = v_fn_1617_;
v_x_1552_ = v___x_1619_;
v_x_1553_ = v___x_1621_;
goto _start;
}
else
{
lean_dec(v_x_1553_);
if (v_skipConstInApp_1550_ == 0)
{
goto v___jp_1612_;
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = l_Lean_Expr_isConst(v_x_1551_);
if (v___x_1623_ == 0)
{
goto v___jp_1612_;
}
else
{
v_f_1562_ = v_x_1551_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v___y_1555_;
v___y_1565_ = v___y_1556_;
v___y_1566_ = v___y_1557_;
v___y_1567_ = v___y_1558_;
v___y_1568_ = v___y_1559_;
goto v___jp_1561_;
}
}
}
v___jp_1561_:
{
if (v_skipInstances_1546_ == 0)
{
size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_sz_1569_ = lean_array_size(v_x_1552_);
v___x_1570_ = ((size_t)0ULL);
lean_inc_ref(v_post_1548_);
lean_inc_ref(v_pre_1547_);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1546_, v_sz_1569_, v___x_1570_, v_x_1552_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v_fst_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_fst_1573_);
v_snd_1574_ = lean_ctor_get(v_a_1572_, 1);
lean_inc(v_snd_1574_);
lean_dec(v_a_1572_);
v___x_1575_ = l_Lean_mkAppN(v_f_1562_, v_fst_1573_);
lean_dec(v_fst_1573_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1546_, v___x_1575_, v___y_1563_, v_snd_1574_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1576_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_f_1562_);
lean_dec_ref(v_post_1548_);
lean_dec_ref(v_pre_1547_);
v_a_1577_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1571_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1571_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
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
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_array_get_size(v_x_1552_);
lean_inc_ref(v_f_1562_);
v___x_1586_ = l_Lean_Meta_getFunInfoNArgs(v_f_1562_, v___x_1585_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v_paramInfo_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
v_paramInfo_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc_ref(v_paramInfo_1588_);
lean_dec(v_a_1587_);
v___x_1589_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1548_);
lean_inc_ref(v_pre_1547_);
v___x_1590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1585_, v_paramInfo_1588_, v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1546_, v___x_1589_, v_x_1552_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec_ref(v_paramInfo_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v_fst_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_fst_1592_);
v_snd_1593_ = lean_ctor_get(v_a_1591_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1591_);
v___x_1594_ = l_Lean_mkAppN(v_f_1562_, v_fst_1592_);
lean_dec(v_fst_1592_);
v___x_1595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1546_, v___x_1594_, v___y_1563_, v_snd_1593_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1595_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_f_1562_);
lean_dec_ref(v_post_1548_);
lean_dec_ref(v_pre_1547_);
v_a_1596_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1590_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1590_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v___y_1564_);
lean_dec_ref(v_f_1562_);
lean_dec_ref(v_x_1552_);
lean_dec_ref(v_post_1548_);
lean_dec_ref(v_pre_1547_);
v_a_1604_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1586_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1586_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
v___jp_1612_:
{
lean_object* v___x_1613_; 
lean_inc_ref(v_post_1548_);
lean_inc_ref(v_pre_1547_);
v___x_1613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1546_, v_x_1551_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v_fst_1615_; lean_object* v_snd_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v_fst_1615_ = lean_ctor_get(v_a_1614_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v_a_1614_, 1);
lean_inc(v_snd_1616_);
lean_dec(v_a_1614_);
v_f_1562_ = v_fst_1615_;
v___y_1563_ = v___y_1554_;
v___y_1564_ = v_snd_1616_;
v___y_1565_ = v___y_1556_;
v___y_1566_ = v___y_1557_;
v___y_1567_ = v___y_1558_;
v___y_1568_ = v___y_1559_;
goto v___jp_1561_;
}
else
{
lean_dec_ref(v_x_1552_);
lean_dec_ref(v_post_1548_);
lean_dec_ref(v_pre_1547_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1624_, lean_object* v_pre_1625_, lean_object* v_e_1626_, lean_object* v_post_1627_, uint8_t v_usedLetOnly_1628_, uint8_t v_skipConstInApp_1629_, uint8_t v_skipInstances_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Core_checkSystem(v___x_1624_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v___x_1638_);
lean_inc_ref(v_pre_1625_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc_ref(v_e_1626_);
v___x_1639_ = lean_apply_7(v_pre_1625_, v_e_1626_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1701_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1701_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1701_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_fst_1644_; lean_object* v_snd_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1700_; 
v_fst_1644_ = lean_ctor_get(v_a_1640_, 0);
v_snd_1645_ = lean_ctor_get(v_a_1640_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1647_ = v_a_1640_;
v_isShared_1648_ = v_isSharedCheck_1700_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snd_1645_);
lean_inc(v_fst_1644_);
lean_dec(v_a_1640_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1700_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___y_1650_; 
switch(lean_obj_tag(v_fst_1644_))
{
case 0:
{
lean_object* v_e_1689_; lean_object* v___x_1691_; 
lean_dec_ref(v_post_1627_);
lean_dec_ref(v_e_1626_);
lean_dec_ref(v_pre_1625_);
v_e_1689_ = lean_ctor_get(v_fst_1644_, 0);
lean_inc_ref(v_e_1689_);
lean_dec_ref(v_fst_1644_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v_e_1689_);
v___x_1691_ = v___x_1647_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_e_1689_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_snd_1645_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1691_);
v___x_1693_ = v___x_1642_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
case 1:
{
lean_object* v_e_1696_; lean_object* v___x_1697_; 
lean_del_object(v___x_1647_);
lean_del_object(v___x_1642_);
lean_dec_ref(v_e_1626_);
v_e_1696_ = lean_ctor_get(v_fst_1644_, 0);
lean_inc_ref(v_e_1696_);
lean_dec_ref(v_fst_1644_);
v___x_1697_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v_e_1696_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1697_;
}
default: 
{
lean_object* v_e_x3f_1698_; 
lean_del_object(v___x_1647_);
lean_del_object(v___x_1642_);
v_e_x3f_1698_ = lean_ctor_get(v_fst_1644_, 0);
lean_inc(v_e_x3f_1698_);
lean_dec_ref(v_fst_1644_);
if (lean_obj_tag(v_e_x3f_1698_) == 0)
{
v___y_1650_ = v_e_1626_;
goto v___jp_1649_;
}
else
{
lean_object* v_val_1699_; 
lean_dec_ref(v_e_1626_);
v_val_1699_ = lean_ctor_get(v_e_x3f_1698_, 0);
lean_inc(v_val_1699_);
lean_dec_ref(v_e_x3f_1698_);
v___y_1650_ = v_val_1699_;
goto v___jp_1649_;
}
}
}
v___jp_1649_:
{
switch(lean_obj_tag(v___y_1650_))
{
case 7:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___x_1651_, v___y_1650_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1652_;
}
case 6:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___x_1653_, v___y_1650_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1654_;
}
case 8:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___x_1655_, v___y_1650_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1656_;
}
case 5:
{
lean_object* v_dummy_1657_; lean_object* v_nargs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_dummy_1657_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1658_ = l_Lean_Expr_getAppNumArgs(v___y_1650_);
lean_inc(v_nargs_1658_);
v___x_1659_ = lean_mk_array(v_nargs_1658_, v_dummy_1657_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_sub(v_nargs_1658_, v___x_1660_);
lean_dec(v_nargs_1658_);
v___x_1662_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1630_, v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v___y_1650_, v___x_1659_, v___x_1661_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1662_;
}
case 10:
{
lean_object* v_data_1663_; lean_object* v_expr_1664_; lean_object* v___x_1665_; 
v_data_1663_ = lean_ctor_get(v___y_1650_, 0);
v_expr_1664_ = lean_ctor_get(v___y_1650_, 1);
lean_inc_ref(v_expr_1664_);
lean_inc_ref(v_post_1627_);
lean_inc_ref(v_pre_1625_);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v_expr_1664_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v_fst_1667_; lean_object* v_snd_1668_; size_t v___x_1669_; size_t v___x_1670_; uint8_t v___x_1671_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v___x_1665_);
v_fst_1667_ = lean_ctor_get(v_a_1666_, 0);
lean_inc(v_fst_1667_);
v_snd_1668_ = lean_ctor_get(v_a_1666_, 1);
lean_inc(v_snd_1668_);
lean_dec(v_a_1666_);
v___x_1669_ = lean_ptr_addr(v_expr_1664_);
v___x_1670_ = lean_ptr_addr(v_fst_1667_);
v___x_1671_ = lean_usize_dec_eq(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_inc(v_data_1663_);
lean_dec_ref(v___y_1650_);
v___x_1672_ = l_Lean_Expr_mdata___override(v_data_1663_, v_fst_1667_);
v___x_1673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___x_1672_, v___y_1631_, v_snd_1668_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; 
lean_dec(v_fst_1667_);
v___x_1674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___y_1650_, v___y_1631_, v_snd_1668_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1674_;
}
}
else
{
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_post_1627_);
lean_dec_ref(v_pre_1625_);
return v___x_1665_;
}
}
case 11:
{
lean_object* v_typeName_1675_; lean_object* v_idx_1676_; lean_object* v_struct_1677_; lean_object* v___x_1678_; 
v_typeName_1675_ = lean_ctor_get(v___y_1650_, 0);
v_idx_1676_ = lean_ctor_get(v___y_1650_, 1);
v_struct_1677_ = lean_ctor_get(v___y_1650_, 2);
lean_inc_ref(v_struct_1677_);
lean_inc_ref(v_post_1627_);
lean_inc_ref(v_pre_1625_);
v___x_1678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v_struct_1677_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v_fst_1680_; lean_object* v_snd_1681_; size_t v___x_1682_; size_t v___x_1683_; uint8_t v___x_1684_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1678_);
v_fst_1680_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_fst_1680_);
v_snd_1681_ = lean_ctor_get(v_a_1679_, 1);
lean_inc(v_snd_1681_);
lean_dec(v_a_1679_);
v___x_1682_ = lean_ptr_addr(v_struct_1677_);
v___x_1683_ = lean_ptr_addr(v_fst_1680_);
v___x_1684_ = lean_usize_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc(v_idx_1676_);
lean_inc(v_typeName_1675_);
lean_dec_ref(v___y_1650_);
v___x_1685_ = l_Lean_Expr_proj___override(v_typeName_1675_, v_idx_1676_, v_fst_1680_);
v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___x_1685_, v___y_1631_, v_snd_1681_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_fst_1680_);
v___x_1687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___y_1650_, v___y_1631_, v_snd_1681_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1687_;
}
}
else
{
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_post_1627_);
lean_dec_ref(v_pre_1625_);
return v___x_1678_;
}
}
default: 
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1625_, v_post_1627_, v_usedLetOnly_1628_, v_skipConstInApp_1629_, v_skipInstances_1630_, v___y_1650_, v___y_1631_, v_snd_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1688_;
}
}
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_post_1627_);
lean_dec_ref(v_e_1626_);
lean_dec_ref(v_pre_1625_);
v_a_1702_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1639_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1639_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v___y_1632_);
lean_dec_ref(v_post_1627_);
lean_dec_ref(v_e_1626_);
lean_dec_ref(v_pre_1625_);
v_a_1710_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1638_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1638_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1718_, lean_object* v_pre_1719_, lean_object* v_e_1720_, lean_object* v_post_1721_, lean_object* v_usedLetOnly_1722_, lean_object* v_skipConstInApp_1723_, lean_object* v_skipInstances_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v_usedLetOnly_boxed_1732_; uint8_t v_skipConstInApp_boxed_1733_; uint8_t v_skipInstances_boxed_1734_; lean_object* v_res_1735_; 
v_usedLetOnly_boxed_1732_ = lean_unbox(v_usedLetOnly_1722_);
v_skipConstInApp_boxed_1733_ = lean_unbox(v_skipConstInApp_1723_);
v_skipInstances_boxed_1734_ = lean_unbox(v_skipInstances_1724_);
v_res_1735_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1718_, v_pre_1719_, v_e_1720_, v_post_1721_, v_usedLetOnly_boxed_1732_, v_skipConstInApp_boxed_1733_, v_skipInstances_boxed_1734_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1725_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1736_, lean_object* v_post_1737_, uint8_t v_usedLetOnly_1738_, uint8_t v_skipConstInApp_1739_, uint8_t v_skipInstances_1740_, lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_inc(v_a_1742_);
v___x_1749_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1749_, 0, lean_box(0));
lean_closure_set(v___x_1749_, 1, lean_box(0));
lean_closure_set(v___x_1749_, 2, v_a_1742_);
v___x_1750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1749_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1805_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1805_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1805_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_fst_1755_; lean_object* v_snd_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1804_; 
v_fst_1755_ = lean_ctor_get(v_a_1751_, 0);
v_snd_1756_ = lean_ctor_get(v_a_1751_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_a_1751_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1758_ = v_a_1751_;
v_isShared_1759_ = v_isSharedCheck_1804_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snd_1756_);
lean_inc(v_fst_1755_);
lean_dec(v_a_1751_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1804_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1755_, v_e_1741_);
lean_dec(v_fst_1755_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; 
lean_del_object(v___x_1758_);
lean_del_object(v___x_1753_);
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1762_ = lean_box(v_usedLetOnly_1738_);
v___x_1763_ = lean_box(v_skipConstInApp_1739_);
v___x_1764_ = lean_box(v_skipInstances_1740_);
lean_inc_ref(v_e_1741_);
v___f_1765_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1765_, 0, v___x_1761_);
lean_closure_set(v___f_1765_, 1, v_pre_1736_);
lean_closure_set(v___f_1765_, 2, v_e_1741_);
lean_closure_set(v___f_1765_, 3, v_post_1737_);
lean_closure_set(v___f_1765_, 4, v___x_1762_);
lean_closure_set(v___f_1765_, 5, v___x_1763_);
lean_closure_set(v___f_1765_, 6, v___x_1764_);
v___x_1766_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1765_, v_a_1742_, v_snd_1756_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v_fst_1768_ = lean_ctor_get(v_a_1767_, 0);
lean_inc_n(v_fst_1768_, 2);
v_snd_1769_ = lean_ctor_get(v_a_1767_, 1);
lean_inc(v_snd_1769_);
lean_dec(v_a_1767_);
lean_inc(v_a_1742_);
v___f_1770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1770_, 0, v_a_1742_);
lean_closure_set(v___f_1770_, 1, v_e_1741_);
lean_closure_set(v___f_1770_, 2, v_fst_1768_);
v___x_1771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1770_, v_snd_1769_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1788_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1788_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1788_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_snd_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_snd_1776_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_a_1772_, 0);
lean_dec(v_unused_1787_);
v___x_1778_ = v_a_1772_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snd_1776_);
lean_dec(v_a_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_fst_1768_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1768_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1776_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1781_);
v___x_1783_ = v___x_1774_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_fst_1768_);
v_a_1789_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1771_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1771_);
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
else
{
lean_dec_ref(v_e_1741_);
return v___x_1766_;
}
}
else
{
lean_object* v_val_1797_; lean_object* v___x_1799_; 
lean_dec_ref(v_e_1741_);
lean_dec_ref(v_post_1737_);
lean_dec_ref(v_pre_1736_);
v_val_1797_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1797_);
lean_dec_ref(v___x_1760_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v_val_1797_);
v___x_1799_ = v___x_1758_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_val_1797_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_snd_1756_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1799_);
v___x_1801_ = v___x_1753_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec_ref(v_e_1741_);
lean_dec_ref(v_post_1737_);
lean_dec_ref(v_pre_1736_);
v_a_1806_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1750_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1750_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1814_, lean_object* v_pre_1815_, lean_object* v_post_1816_, lean_object* v_usedLetOnly_1817_, lean_object* v_skipConstInApp_1818_, lean_object* v_skipInstances_1819_, lean_object* v_body_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v_usedLetOnly_boxed_1829_; uint8_t v_skipConstInApp_boxed_1830_; uint8_t v_skipInstances_boxed_1831_; lean_object* v_res_1832_; 
v_usedLetOnly_boxed_1829_ = lean_unbox(v_usedLetOnly_1817_);
v_skipConstInApp_boxed_1830_ = lean_unbox(v_skipConstInApp_1818_);
v_skipInstances_boxed_1831_ = lean_unbox(v_skipInstances_1819_);
v_res_1832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1814_, v_pre_1815_, v_post_1816_, v_usedLetOnly_boxed_1829_, v_skipConstInApp_boxed_1830_, v_skipInstances_boxed_1831_, v_body_1820_, v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1822_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1833_, lean_object* v_post_1834_, uint8_t v_usedLetOnly_1835_, uint8_t v_skipConstInApp_1836_, uint8_t v_skipInstances_1837_, lean_object* v_fvars_1838_, lean_object* v_e_1839_, lean_object* v_a_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
if (lean_obj_tag(v_e_1839_) == 7)
{
lean_object* v_binderName_1847_; lean_object* v_binderType_1848_; lean_object* v_body_1849_; uint8_t v_binderInfo_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_binderName_1847_ = lean_ctor_get(v_e_1839_, 0);
lean_inc(v_binderName_1847_);
v_binderType_1848_ = lean_ctor_get(v_e_1839_, 1);
lean_inc_ref(v_binderType_1848_);
v_body_1849_ = lean_ctor_get(v_e_1839_, 2);
lean_inc_ref(v_body_1849_);
v_binderInfo_1850_ = lean_ctor_get_uint8(v_e_1839_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1839_);
v___x_1851_ = lean_expr_instantiate_rev(v_binderType_1848_, v_fvars_1838_);
lean_dec_ref(v_binderType_1848_);
lean_inc_ref(v_post_1834_);
lean_inc_ref(v_pre_1833_);
v___x_1852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1833_, v_post_1834_, v_usedLetOnly_1835_, v_skipConstInApp_1836_, v_skipInstances_1837_, v___x_1851_, v_a_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___f_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v_fst_1854_ = lean_ctor_get(v_a_1853_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v_a_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_a_1853_);
v___x_1856_ = lean_box(v_usedLetOnly_1835_);
v___x_1857_ = lean_box(v_skipConstInApp_1836_);
v___x_1858_ = lean_box(v_skipInstances_1837_);
v___f_1859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1859_, 0, v_fvars_1838_);
lean_closure_set(v___f_1859_, 1, v_pre_1833_);
lean_closure_set(v___f_1859_, 2, v_post_1834_);
lean_closure_set(v___f_1859_, 3, v___x_1856_);
lean_closure_set(v___f_1859_, 4, v___x_1857_);
lean_closure_set(v___f_1859_, 5, v___x_1858_);
lean_closure_set(v___f_1859_, 6, v_body_1849_);
v___x_1860_ = 0;
v___x_1861_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1847_, v_binderInfo_1850_, v_fst_1854_, v___f_1859_, v___x_1860_, v_a_1840_, v_snd_1855_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1861_;
}
else
{
lean_dec_ref(v_body_1849_);
lean_dec(v_binderName_1847_);
lean_dec_ref(v_fvars_1838_);
lean_dec_ref(v_post_1834_);
lean_dec_ref(v_pre_1833_);
return v___x_1852_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_expr_instantiate_rev(v_e_1839_, v_fvars_1838_);
lean_dec_ref(v_e_1839_);
lean_inc_ref(v_post_1834_);
lean_inc_ref(v_pre_1833_);
v___x_1863_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1833_, v_post_1834_, v_usedLetOnly_1835_, v_skipConstInApp_1836_, v_skipInstances_1837_, v___x_1862_, v_a_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; uint8_t v___x_1867_; uint8_t v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v_fst_1865_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_fst_1865_);
v_snd_1866_ = lean_ctor_get(v_a_1864_, 1);
lean_inc(v_snd_1866_);
lean_dec(v_a_1864_);
v___x_1867_ = 0;
v___x_1868_ = 1;
v___x_1869_ = 1;
v___x_1870_ = l_Lean_Meta_mkForallFVars(v_fvars_1838_, v_fst_1865_, v___x_1867_, v_usedLetOnly_1835_, v___x_1868_, v___x_1869_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v_fvars_1838_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1833_, v_post_1834_, v_usedLetOnly_1835_, v_skipConstInApp_1836_, v_skipInstances_1837_, v_a_1871_, v_a_1840_, v_snd_1866_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1872_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_snd_1866_);
lean_dec_ref(v_post_1834_);
lean_dec_ref(v_pre_1833_);
v_a_1873_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1870_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1870_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1838_);
lean_dec_ref(v_post_1834_);
lean_dec_ref(v_pre_1833_);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1881_, lean_object* v_pre_1882_, lean_object* v_post_1883_, uint8_t v_usedLetOnly_1884_, uint8_t v_skipConstInApp_1885_, uint8_t v_skipInstances_1886_, lean_object* v_body_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_array_push(v_fvars_1881_, v_x_1888_);
v___x_1897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1886_, v___x_1896_, v_body_1887_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1898_, lean_object* v_post_1899_, lean_object* v_usedLetOnly_1900_, lean_object* v_skipConstInApp_1901_, lean_object* v_skipInstances_1902_, lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_bs_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v_usedLetOnly_boxed_1913_; uint8_t v_skipConstInApp_boxed_1914_; uint8_t v_skipInstances_boxed_1915_; size_t v_sz_boxed_1916_; size_t v_i_boxed_1917_; lean_object* v_res_1918_; 
v_usedLetOnly_boxed_1913_ = lean_unbox(v_usedLetOnly_1900_);
v_skipConstInApp_boxed_1914_ = lean_unbox(v_skipConstInApp_1901_);
v_skipInstances_boxed_1915_ = lean_unbox(v_skipInstances_1902_);
v_sz_boxed_1916_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1917_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1898_, v_post_1899_, v_usedLetOnly_boxed_1913_, v_skipConstInApp_boxed_1914_, v_skipInstances_boxed_1915_, v_sz_boxed_1916_, v_i_boxed_1917_, v_bs_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1906_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1919_, lean_object* v_post_1920_, lean_object* v_usedLetOnly_1921_, lean_object* v_skipConstInApp_1922_, lean_object* v_skipInstances_1923_, lean_object* v_e_1924_, lean_object* v_a_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_usedLetOnly_boxed_1932_; uint8_t v_skipConstInApp_boxed_1933_; uint8_t v_skipInstances_boxed_1934_; lean_object* v_res_1935_; 
v_usedLetOnly_boxed_1932_ = lean_unbox(v_usedLetOnly_1921_);
v_skipConstInApp_boxed_1933_ = lean_unbox(v_skipConstInApp_1922_);
v_skipInstances_boxed_1934_ = lean_unbox(v_skipInstances_1923_);
v_res_1935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1919_, v_post_1920_, v_usedLetOnly_boxed_1932_, v_skipConstInApp_boxed_1933_, v_skipInstances_boxed_1934_, v_e_1924_, v_a_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_a_1925_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1936_, lean_object* v_post_1937_, lean_object* v_usedLetOnly_1938_, lean_object* v_skipConstInApp_1939_, lean_object* v_skipInstances_1940_, lean_object* v_fvars_1941_, lean_object* v_e_1942_, lean_object* v_a_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v_usedLetOnly_boxed_1950_; uint8_t v_skipConstInApp_boxed_1951_; uint8_t v_skipInstances_boxed_1952_; lean_object* v_res_1953_; 
v_usedLetOnly_boxed_1950_ = lean_unbox(v_usedLetOnly_1938_);
v_skipConstInApp_boxed_1951_ = lean_unbox(v_skipConstInApp_1939_);
v_skipInstances_boxed_1952_ = lean_unbox(v_skipInstances_1940_);
v_res_1953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1936_, v_post_1937_, v_usedLetOnly_boxed_1950_, v_skipConstInApp_boxed_1951_, v_skipInstances_boxed_1952_, v_fvars_1941_, v_e_1942_, v_a_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v_a_1943_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1954_, lean_object* v_post_1955_, lean_object* v_usedLetOnly_1956_, lean_object* v_skipConstInApp_1957_, lean_object* v_skipInstances_1958_, lean_object* v_fvars_1959_, lean_object* v_e_1960_, lean_object* v_a_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_usedLetOnly_boxed_1968_; uint8_t v_skipConstInApp_boxed_1969_; uint8_t v_skipInstances_boxed_1970_; lean_object* v_res_1971_; 
v_usedLetOnly_boxed_1968_ = lean_unbox(v_usedLetOnly_1956_);
v_skipConstInApp_boxed_1969_ = lean_unbox(v_skipConstInApp_1957_);
v_skipInstances_boxed_1970_ = lean_unbox(v_skipInstances_1958_);
v_res_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1954_, v_post_1955_, v_usedLetOnly_boxed_1968_, v_skipConstInApp_boxed_1969_, v_skipInstances_boxed_1970_, v_fvars_1959_, v_e_1960_, v_a_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v_a_1961_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1972_, lean_object* v_post_1973_, lean_object* v_usedLetOnly_1974_, lean_object* v_skipConstInApp_1975_, lean_object* v_skipInstances_1976_, lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v_usedLetOnly_boxed_1985_; uint8_t v_skipConstInApp_boxed_1986_; uint8_t v_skipInstances_boxed_1987_; lean_object* v_res_1988_; 
v_usedLetOnly_boxed_1985_ = lean_unbox(v_usedLetOnly_1974_);
v_skipConstInApp_boxed_1986_ = lean_unbox(v_skipConstInApp_1975_);
v_skipInstances_boxed_1987_ = lean_unbox(v_skipInstances_1976_);
v_res_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1972_, v_post_1973_, v_usedLetOnly_boxed_1985_, v_skipConstInApp_boxed_1986_, v_skipInstances_boxed_1987_, v_e_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_a_1978_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1989_, lean_object* v_post_1990_, lean_object* v_usedLetOnly_1991_, lean_object* v_skipConstInApp_1992_, lean_object* v_skipInstances_1993_, lean_object* v_fvars_1994_, lean_object* v_e_1995_, lean_object* v_a_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v_usedLetOnly_boxed_2003_; uint8_t v_skipConstInApp_boxed_2004_; uint8_t v_skipInstances_boxed_2005_; lean_object* v_res_2006_; 
v_usedLetOnly_boxed_2003_ = lean_unbox(v_usedLetOnly_1991_);
v_skipConstInApp_boxed_2004_ = lean_unbox(v_skipConstInApp_1992_);
v_skipInstances_boxed_2005_ = lean_unbox(v_skipInstances_1993_);
v_res_2006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1989_, v_post_1990_, v_usedLetOnly_boxed_2003_, v_skipConstInApp_boxed_2004_, v_skipInstances_boxed_2005_, v_fvars_1994_, v_e_1995_, v_a_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_a_1996_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_2007_, lean_object* v___x_2008_, lean_object* v_pre_2009_, lean_object* v_post_2010_, lean_object* v_usedLetOnly_2011_, lean_object* v_skipConstInApp_2012_, lean_object* v_skipInstances_2013_, lean_object* v_a_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v_usedLetOnly_boxed_2023_; uint8_t v_skipConstInApp_boxed_2024_; uint8_t v_skipInstances_boxed_2025_; lean_object* v_res_2026_; 
v_usedLetOnly_boxed_2023_ = lean_unbox(v_usedLetOnly_2011_);
v_skipConstInApp_boxed_2024_ = lean_unbox(v_skipConstInApp_2012_);
v_skipInstances_boxed_2025_ = lean_unbox(v_skipInstances_2013_);
v_res_2026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2007_, v___x_2008_, v_pre_2009_, v_post_2010_, v_usedLetOnly_boxed_2023_, v_skipConstInApp_boxed_2024_, v_skipInstances_boxed_2025_, v_a_2014_, v_b_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2016_);
lean_dec_ref(v___x_2008_);
lean_dec(v_upperBound_2007_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2027_, lean_object* v_pre_2028_, lean_object* v_post_2029_, lean_object* v_usedLetOnly_2030_, lean_object* v_skipConstInApp_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v_skipInstances_boxed_2042_; uint8_t v_usedLetOnly_boxed_2043_; uint8_t v_skipConstInApp_boxed_2044_; lean_object* v_res_2045_; 
v_skipInstances_boxed_2042_ = lean_unbox(v_skipInstances_2027_);
v_usedLetOnly_boxed_2043_ = lean_unbox(v_usedLetOnly_2030_);
v_skipConstInApp_boxed_2044_ = lean_unbox(v_skipConstInApp_2031_);
v_res_2045_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2042_, v_pre_2028_, v_post_2029_, v_usedLetOnly_boxed_2043_, v_skipConstInApp_boxed_2044_, v_x_2032_, v_x_2033_, v_x_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2035_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_apply_1(v_x_2047_, lean_box(0));
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___y_2048_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2057_, v_x_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_unsigned_to_nat(16u);
v___x_2068_ = lean_mk_array(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2073_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2073_, 0, lean_box(0));
lean_closure_set(v___x_2073_, 1, lean_box(0));
lean_closure_set(v___x_2073_, 2, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2074_, lean_object* v_pre_2075_, lean_object* v_post_2076_, uint8_t v_usedLetOnly_2077_, uint8_t v_skipConstInApp_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2086_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2085_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
v_fst_2088_ = lean_ctor_get(v_a_2087_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_a_2087_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_a_2087_);
v___x_2090_ = 0;
v___x_2091_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2075_, v_post_2076_, v_usedLetOnly_2077_, v_skipConstInApp_2078_, v___x_2090_, v_input_2074_, v_fst_2088_, v_snd_2089_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2113_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v_fst_2093_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_fst_2093_);
v_snd_2094_ = lean_ctor_get(v_a_2092_, 1);
lean_inc(v_snd_2094_);
lean_dec(v_a_2092_);
v___x_2095_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2095_, 0, lean_box(0));
lean_closure_set(v___x_2095_, 1, lean_box(0));
lean_closure_set(v___x_2095_, 2, v_fst_2088_);
v___x_2096_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2095_, v_snd_2094_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2113_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2113_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_snd_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2111_; 
v_snd_2101_ = lean_ctor_get(v_a_2097_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_a_2097_, 0);
lean_dec(v_unused_2112_);
v___x_2103_ = v_a_2097_;
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snd_2101_);
lean_dec(v_a_2097_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v_fst_2093_);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fst_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2101_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2106_);
v___x_2108_ = v___x_2099_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_dec(v_fst_2088_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2114_, lean_object* v_pre_2115_, lean_object* v_post_2116_, lean_object* v_usedLetOnly_2117_, lean_object* v_skipConstInApp_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_usedLetOnly_boxed_2125_; uint8_t v_skipConstInApp_boxed_2126_; lean_object* v_res_2127_; 
v_usedLetOnly_boxed_2125_ = lean_unbox(v_usedLetOnly_2117_);
v_skipConstInApp_boxed_2126_ = lean_unbox(v_skipConstInApp_2118_);
v_res_2127_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2114_, v_pre_2115_, v_post_2116_, v_usedLetOnly_boxed_2125_, v_skipConstInApp_boxed_2126_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2127_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2130_; uint64_t v___x_2131_; 
v___x_2130_ = 3;
v___x_2131_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; uint8_t v_foApprox_2139_; uint8_t v_ctxApprox_2140_; uint8_t v_quasiPatternApprox_2141_; uint8_t v_constApprox_2142_; uint8_t v_isDefEqStuckEx_2143_; uint8_t v_unificationHints_2144_; uint8_t v_proofIrrelevance_2145_; uint8_t v_assignSyntheticOpaque_2146_; uint8_t v_offsetCnstrs_2147_; uint8_t v_etaStruct_2148_; uint8_t v_univApprox_2149_; uint8_t v_iota_2150_; uint8_t v_beta_2151_; uint8_t v_proj_2152_; uint8_t v_zeta_2153_; uint8_t v_zetaDelta_2154_; uint8_t v_zetaUnused_2155_; uint8_t v_zetaHave_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2187_; 
v___x_2138_ = l_Lean_Meta_Context_config(v_a_2133_);
v_foApprox_2139_ = lean_ctor_get_uint8(v___x_2138_, 0);
v_ctxApprox_2140_ = lean_ctor_get_uint8(v___x_2138_, 1);
v_quasiPatternApprox_2141_ = lean_ctor_get_uint8(v___x_2138_, 2);
v_constApprox_2142_ = lean_ctor_get_uint8(v___x_2138_, 3);
v_isDefEqStuckEx_2143_ = lean_ctor_get_uint8(v___x_2138_, 4);
v_unificationHints_2144_ = lean_ctor_get_uint8(v___x_2138_, 5);
v_proofIrrelevance_2145_ = lean_ctor_get_uint8(v___x_2138_, 6);
v_assignSyntheticOpaque_2146_ = lean_ctor_get_uint8(v___x_2138_, 7);
v_offsetCnstrs_2147_ = lean_ctor_get_uint8(v___x_2138_, 8);
v_etaStruct_2148_ = lean_ctor_get_uint8(v___x_2138_, 10);
v_univApprox_2149_ = lean_ctor_get_uint8(v___x_2138_, 11);
v_iota_2150_ = lean_ctor_get_uint8(v___x_2138_, 12);
v_beta_2151_ = lean_ctor_get_uint8(v___x_2138_, 13);
v_proj_2152_ = lean_ctor_get_uint8(v___x_2138_, 14);
v_zeta_2153_ = lean_ctor_get_uint8(v___x_2138_, 15);
v_zetaDelta_2154_ = lean_ctor_get_uint8(v___x_2138_, 16);
v_zetaUnused_2155_ = lean_ctor_get_uint8(v___x_2138_, 17);
v_zetaHave_2156_ = lean_ctor_get_uint8(v___x_2138_, 18);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2158_ = v___x_2138_;
v_isShared_2159_ = v_isSharedCheck_2187_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2138_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2187_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
uint8_t v_trackZetaDelta_2160_; lean_object* v_zetaDeltaSet_2161_; lean_object* v_lctx_2162_; lean_object* v_localInstances_2163_; lean_object* v_defEqCtx_x3f_2164_; lean_object* v_synthPendingDepth_2165_; lean_object* v_canUnfold_x3f_2166_; uint8_t v_univApprox_2167_; uint8_t v_inTypeClassResolution_2168_; uint8_t v_cacheInferType_2169_; uint8_t v___x_2170_; lean_object* v_config_2172_; 
v_trackZetaDelta_2160_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*7);
v_zetaDeltaSet_2161_ = lean_ctor_get(v_a_2133_, 1);
v_lctx_2162_ = lean_ctor_get(v_a_2133_, 2);
v_localInstances_2163_ = lean_ctor_get(v_a_2133_, 3);
v_defEqCtx_x3f_2164_ = lean_ctor_get(v_a_2133_, 4);
v_synthPendingDepth_2165_ = lean_ctor_get(v_a_2133_, 5);
v_canUnfold_x3f_2166_ = lean_ctor_get(v_a_2133_, 6);
v_univApprox_2167_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2168_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*7 + 2);
v_cacheInferType_2169_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*7 + 3);
v___x_2170_ = 3;
if (v_isShared_2159_ == 0)
{
v_config_2172_ = v___x_2158_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 0, v_foApprox_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 1, v_ctxApprox_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 2, v_quasiPatternApprox_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 3, v_constApprox_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 4, v_isDefEqStuckEx_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 5, v_unificationHints_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 6, v_proofIrrelevance_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 7, v_assignSyntheticOpaque_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 8, v_offsetCnstrs_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 10, v_etaStruct_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 11, v_univApprox_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 12, v_iota_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 13, v_beta_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 14, v_proj_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 15, v_zeta_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 16, v_zetaDelta_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 17, v_zetaUnused_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, 18, v_zetaHave_2156_);
v_config_2172_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
uint64_t v___x_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; lean_object* v___f_2176_; lean_object* v___f_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; uint64_t v_key_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_ctor_set_uint8(v_config_2172_, 9, v___x_2170_);
v___x_2173_ = l_Lean_Meta_Context_configKey(v_a_2133_);
v___x_2174_ = 2ULL;
v___x_2175_ = lean_uint64_shift_right(v___x_2173_, v___x_2174_);
v___f_2176_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2177_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2178_ = 0;
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_uint64_shift_left(v___x_2175_, v___x_2174_);
v___x_2181_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2182_ = lean_uint64_lor(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2183_, 0, v_config_2172_);
lean_ctor_set_uint64(v___x_2183_, sizeof(void*)*1, v_key_2182_);
lean_inc(v_canUnfold_x3f_2166_);
lean_inc(v_synthPendingDepth_2165_);
lean_inc(v_defEqCtx_x3f_2164_);
lean_inc_ref(v_localInstances_2163_);
lean_inc_ref(v_lctx_2162_);
lean_inc(v_zetaDeltaSet_2161_);
v___x_2184_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v_zetaDeltaSet_2161_);
lean_ctor_set(v___x_2184_, 2, v_lctx_2162_);
lean_ctor_set(v___x_2184_, 3, v_localInstances_2163_);
lean_ctor_set(v___x_2184_, 4, v_defEqCtx_x3f_2164_);
lean_ctor_set(v___x_2184_, 5, v_synthPendingDepth_2165_);
lean_ctor_set(v___x_2184_, 6, v_canUnfold_x3f_2166_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*7, v_trackZetaDelta_2160_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*7 + 1, v_univApprox_2167_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2168_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*7 + 3, v_cacheInferType_2169_);
v___x_2185_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2132_, v___f_2177_, v___f_2176_, v___x_2178_, v___x_2178_, v___x_2179_, v___x_2184_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec_ref(v___x_2184_);
return v___x_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_expandCoe(v_e_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2195_, lean_object* v_m_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2196_, v_a_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2199_, lean_object* v_m_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2199_, v_m_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_m_2200_);
return v_res_2202_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2203_, lean_object* v_x_2204_, lean_object* v_x_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2204_, v_x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
uint8_t v_res_2210_; lean_object* v_r_2211_; 
v_res_2210_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2207_, v_x_2208_, v_x_2209_);
lean_dec_ref(v_x_2209_);
lean_dec_ref(v_x_2208_);
v_r_2211_ = lean_box(v_res_2210_);
return v_r_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2212_, lean_object* v_a_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2213_, v_x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_a_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2216_, v_a_2217_, v_x_2218_);
lean_dec(v_x_2218_);
lean_dec(v_a_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2220_, lean_object* v___x_2221_, lean_object* v_pre_2222_, lean_object* v_post_2223_, uint8_t v_usedLetOnly_2224_, uint8_t v_skipConstInApp_2225_, uint8_t v_skipInstances_2226_, lean_object* v___x_2227_, lean_object* v_inst_2228_, lean_object* v_R_2229_, lean_object* v_a_2230_, lean_object* v_b_2231_, lean_object* v_c_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2220_, v___x_2221_, v_pre_2222_, v_post_2223_, v_usedLetOnly_2224_, v_skipConstInApp_2225_, v_skipInstances_2226_, v_a_2230_, v_b_2231_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2241_ = _args[0];
lean_object* v___x_2242_ = _args[1];
lean_object* v_pre_2243_ = _args[2];
lean_object* v_post_2244_ = _args[3];
lean_object* v_usedLetOnly_2245_ = _args[4];
lean_object* v_skipConstInApp_2246_ = _args[5];
lean_object* v_skipInstances_2247_ = _args[6];
lean_object* v___x_2248_ = _args[7];
lean_object* v_inst_2249_ = _args[8];
lean_object* v_R_2250_ = _args[9];
lean_object* v_a_2251_ = _args[10];
lean_object* v_b_2252_ = _args[11];
lean_object* v_c_2253_ = _args[12];
lean_object* v___y_2254_ = _args[13];
lean_object* v___y_2255_ = _args[14];
lean_object* v___y_2256_ = _args[15];
lean_object* v___y_2257_ = _args[16];
lean_object* v___y_2258_ = _args[17];
lean_object* v___y_2259_ = _args[18];
lean_object* v___y_2260_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2261_; uint8_t v_skipConstInApp_boxed_2262_; uint8_t v_skipInstances_boxed_2263_; lean_object* v_res_2264_; 
v_usedLetOnly_boxed_2261_ = lean_unbox(v_usedLetOnly_2245_);
v_skipConstInApp_boxed_2262_ = lean_unbox(v_skipConstInApp_2246_);
v_skipInstances_boxed_2263_ = lean_unbox(v_skipInstances_2247_);
v_res_2264_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2241_, v___x_2242_, v_pre_2243_, v_post_2244_, v_usedLetOnly_boxed_2261_, v_skipConstInApp_boxed_2262_, v_skipInstances_boxed_2263_, v___x_2248_, v_inst_2249_, v_R_2250_, v_a_2251_, v_b_2252_, v_c_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2254_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2242_);
lean_dec(v_upperBound_2241_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2265_, lean_object* v_m_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2266_, v_a_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_m_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2269_, v_m_2270_, v_a_2271_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_m_2270_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2273_, lean_object* v_name_2274_, uint8_t v_bi_2275_, lean_object* v_type_2276_, lean_object* v_k_2277_, uint8_t v_kind_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2274_, v_bi_2275_, v_type_2276_, v_k_2277_, v_kind_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_name_2288_, lean_object* v_bi_2289_, lean_object* v_type_2290_, lean_object* v_k_2291_, lean_object* v_kind_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_bi_boxed_2300_; uint8_t v_kind_boxed_2301_; lean_object* v_res_2302_; 
v_bi_boxed_2300_ = lean_unbox(v_bi_2289_);
v_kind_boxed_2301_ = lean_unbox(v_kind_2292_);
v_res_2302_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2287_, v_name_2288_, v_bi_boxed_2300_, v_type_2290_, v_k_2291_, v_kind_boxed_2301_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2293_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2303_, lean_object* v_name_2304_, lean_object* v_type_2305_, lean_object* v_val_2306_, lean_object* v_k_2307_, uint8_t v_nondep_2308_, uint8_t v_kind_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2304_, v_type_2305_, v_val_2306_, v_k_2307_, v_nondep_2308_, v_kind_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2318_, lean_object* v_name_2319_, lean_object* v_type_2320_, lean_object* v_val_2321_, lean_object* v_k_2322_, lean_object* v_nondep_2323_, lean_object* v_kind_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_nondep_boxed_2332_; uint8_t v_kind_boxed_2333_; lean_object* v_res_2334_; 
v_nondep_boxed_2332_ = lean_unbox(v_nondep_2323_);
v_kind_boxed_2333_ = lean_unbox(v_kind_2324_);
v_res_2334_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2318_, v_name_2319_, v_type_2320_, v_val_2321_, v_k_2322_, v_nondep_boxed_2332_, v_kind_boxed_2333_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2325_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2335_, lean_object* v_ref_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2336_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2343_, lean_object* v_ref_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2343_, v_ref_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2361_, lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2361_, v_x_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2371_, lean_object* v_m_2372_, lean_object* v_a_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2372_, v_a_2373_, v_b_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2376_, lean_object* v_x_2377_, size_t v_x_2378_, lean_object* v_x_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2377_, v_x_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
size_t v_x_40479__boxed_2385_; uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_x_40479__boxed_2385_ = lean_unbox_usize(v_x_2383_);
lean_dec(v_x_2383_);
v_res_2386_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2381_, v_x_2382_, v_x_40479__boxed_2385_, v_x_2384_);
lean_dec_ref(v_x_2384_);
lean_dec_ref(v_x_2382_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2388_, lean_object* v_a_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2389_, v_x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2392_, lean_object* v_a_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2392_, v_a_2393_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2396_, lean_object* v_a_2397_, lean_object* v_x_2398_){
_start:
{
uint8_t v___x_2399_; 
v___x_2399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2397_, v_x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2400_, lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_res_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2400_, v_a_2401_, v_x_2402_);
lean_dec(v_x_2402_);
lean_dec_ref(v_a_2401_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2405_, lean_object* v_data_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2409_, v_b_2410_, v_x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2413_, lean_object* v_keys_2414_, lean_object* v_vals_2415_, lean_object* v_heq_2416_, lean_object* v_i_2417_, lean_object* v_k_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2414_, v_i_2417_, v_k_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2420_, lean_object* v_keys_2421_, lean_object* v_vals_2422_, lean_object* v_heq_2423_, lean_object* v_i_2424_, lean_object* v_k_2425_){
_start:
{
uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_res_2426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2420_, v_keys_2421_, v_vals_2422_, v_heq_2423_, v_i_2424_, v_k_2425_);
lean_dec_ref(v_k_2425_);
lean_dec_ref(v_vals_2422_);
lean_dec_ref(v_keys_2421_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2428_, lean_object* v_i_2429_, lean_object* v_source_2430_, lean_object* v_target_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2429_, v_source_2430_, v_target_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2437_, lean_object* v_decl_2438_, lean_object* v_ref_2439_){
_start:
{
lean_object* v_defValue_2441_; lean_object* v_descr_2442_; lean_object* v_deprecation_x3f_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_defValue_2441_ = lean_ctor_get(v_decl_2438_, 0);
v_descr_2442_ = lean_ctor_get(v_decl_2438_, 1);
v_deprecation_x3f_2443_ = lean_ctor_get(v_decl_2438_, 2);
v___x_2444_ = lean_alloc_ctor(1, 0, 1);
v___x_2445_ = lean_unbox(v_defValue_2441_);
lean_ctor_set_uint8(v___x_2444_, 0, v___x_2445_);
lean_inc(v_deprecation_x3f_2443_);
lean_inc_ref(v_descr_2442_);
lean_inc_n(v_name_2437_, 2);
v___x_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2446_, 0, v_name_2437_);
lean_ctor_set(v___x_2446_, 1, v_ref_2439_);
lean_ctor_set(v___x_2446_, 2, v___x_2444_);
lean_ctor_set(v___x_2446_, 3, v_descr_2442_);
lean_ctor_set(v___x_2446_, 4, v_deprecation_x3f_2443_);
v___x_2447_ = lean_register_option(v_name_2437_, v___x_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2455_; 
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2456_);
v___x_2449_ = v___x_2447_;
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v___x_2447_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_inc(v_defValue_2441_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v_name_2437_);
lean_ctor_set(v___x_2451_, 1, v_defValue_2441_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_name_2437_);
v_a_2457_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2447_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2447_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2465_, lean_object* v_decl_2466_, lean_object* v_ref_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2465_, v_decl_2466_, v_ref_2467_);
lean_dec_ref(v_decl_2466_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2487_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2484_, v___x_2485_, v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_ref_2496_; lean_object* v___x_2497_; lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2506_; 
v_ref_2496_ = lean_ctor_get(v___y_2493_, 5);
v___x_2497_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_inc(v_ref_2496_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_ref_2496_);
lean_ctor_set(v___x_2502_, 1, v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 1);
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2513_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2529_, lean_object* v_expectedType_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2536_; 
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_a_2531_);
lean_inc_ref(v_expr_2529_);
v___x_2536_ = lean_infer_type(v_expr_2529_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_n(v_a_2537_, 2);
lean_dec_ref(v___x_2536_);
v___x_2538_ = l_Lean_Meta_getLevel(v_a_2537_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
lean_inc_ref(v_expectedType_2530_);
v___x_2540_ = l_Lean_Meta_getLevel(v_expectedType_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref(v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2543_ = lean_box(0);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_a_2541_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v_a_2539_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
lean_inc_ref(v___x_2545_);
v___x_2546_ = l_Lean_mkConst(v___x_2542_, v___x_2545_);
v___x_2547_ = lean_unsigned_to_nat(3u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
lean_inc(v_a_2537_);
v___x_2549_ = lean_array_push(v___x_2548_, v_a_2537_);
lean_inc_ref(v_expr_2529_);
v___x_2550_ = lean_array_push(v___x_2549_, v_expr_2529_);
lean_inc_ref(v_expectedType_2530_);
v___x_2551_ = lean_array_push(v___x_2550_, v_expectedType_2530_);
v___x_2552_ = l_Lean_mkAppN(v___x_2546_, v___x_2551_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = lean_box(0);
v___x_2554_ = l_Lean_Meta_trySynthInstance(v___x_2552_, v___x_2553_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2652_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2652_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2652_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
switch(lean_obj_tag(v_a_2555_))
{
case 0:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_dec_ref(v___x_2545_);
lean_dec(v_a_2537_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v___x_2559_ = lean_box(0);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
case 1:
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2557_);
v_a_2563_ = lean_ctor_get(v_a_2555_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2565_ = v_a_2555_;
v_isShared_2566_ = v_isSharedCheck_2647_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v_a_2555_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2647_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2567_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2568_ = l_Lean_mkConst(v___x_2567_, v___x_2545_);
v___x_2569_ = lean_unsigned_to_nat(4u);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2569_);
v___x_2571_ = lean_array_push(v___x_2570_, v_a_2537_);
lean_inc_ref(v_expr_2529_);
v___x_2572_ = lean_array_push(v___x_2571_, v_expr_2529_);
lean_inc_ref(v_expectedType_2530_);
v___x_2573_ = lean_array_push(v___x_2572_, v_expectedType_2530_);
v___x_2574_ = lean_array_push(v___x_2573_, v_a_2563_);
v___x_2575_ = l_Lean_mkAppN(v___x_2568_, v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = l_Lean_Meta_expandCoe(v___x_2575_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2638_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2638_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2638_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_fst_2588_; lean_object* v___x_2589_; 
v_fst_2588_ = lean_ctor_get(v_a_2577_, 0);
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_a_2531_);
lean_inc(v_fst_2588_);
v___x_2589_ = lean_infer_type(v_fst_2588_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
lean_inc_ref(v_expectedType_2530_);
v___x_2591_ = l_Lean_Meta_isExprDefEq(v_a_2590_, v_expectedType_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; uint8_t v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v___x_2593_ = lean_unbox(v_a_2592_);
lean_dec(v_a_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2619_; 
lean_inc(v_fst_2588_);
lean_del_object(v___x_2579_);
lean_del_object(v___x_2565_);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; lean_object* v_unused_2621_; 
v_unused_2620_ = lean_ctor_get(v_a_2577_, 1);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_a_2577_, 0);
lean_dec(v_unused_2621_);
v___x_2595_ = v_a_2577_;
v_isShared_2596_ = v_isSharedCheck_2619_;
goto v_resetjp_2594_;
}
else
{
lean_dec(v_a_2577_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2619_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2598_ = l_Lean_indentExpr(v_expr_2529_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 7);
lean_ctor_set(v___x_2595_, 1, v___x_2598_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v___x_2601_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_indentExpr(v_expectedType_2530_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = l_Lean_indentExpr(v_fst_2588_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2608_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
goto v___jp_2581_;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_del_object(v___x_2579_);
lean_dec(v_a_2577_);
lean_del_object(v___x_2565_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2622_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2591_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2591_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_del_object(v___x_2579_);
lean_dec(v_a_2577_);
lean_del_object(v___x_2565_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2630_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2589_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2589_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
v___jp_2581_:
{
lean_object* v___x_2583_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_a_2577_);
v___x_2583_ = v___x_2565_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2577_);
v___x_2583_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2583_);
v___x_2585_ = v___x_2579_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_del_object(v___x_2565_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2639_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2576_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2576_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
default: 
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_dec_ref(v___x_2545_);
lean_dec(v_a_2537_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v___x_2648_ = lean_box(2);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2648_);
v___x_2650_ = v___x_2557_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v___x_2545_);
lean_dec(v_a_2537_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2653_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2554_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2554_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2539_);
lean_dec(v_a_2537_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2661_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2540_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2540_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2669_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2538_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2538_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v_expectedType_2530_);
lean_dec_ref(v_expr_2529_);
v_a_2677_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2536_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2536_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2685_, lean_object* v_expectedType_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2685_, v_expectedType_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2701_, v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2709_, lean_object* v_expectedType_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2709_, v_expectedType_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2741_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2741_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2741_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
switch(lean_obj_tag(v_a_2717_))
{
case 0:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_box(0);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
case 1:
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2736_; 
v_a_2725_ = lean_ctor_get(v_a_2717_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_a_2717_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2727_ = v_a_2717_;
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v_a_2717_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_fst_2729_; lean_object* v___x_2731_; 
v_fst_2729_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_fst_2729_);
lean_dec(v_a_2725_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v_fst_2729_);
v___x_2731_ = v___x_2727_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_fst_2729_);
v___x_2731_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2731_);
v___x_2733_ = v___x_2719_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
default: 
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = lean_box(2);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2737_);
v___x_2739_ = v___x_2719_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_a_2742_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2716_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2716_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2750_, lean_object* v_expectedType_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2750_, v_expectedType_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___x_2779_; 
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
lean_inc_ref(v_expr_2773_);
v___x_2779_ = lean_infer_type(v_expr_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_n(v_a_2780_, 2);
lean_dec_ref(v___x_2779_);
v___x_2781_ = l_Lean_Meta_getLevel(v_a_2780_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc_n(v_a_2784_, 2);
lean_dec_ref(v___x_2783_);
v___x_2785_ = l_Lean_mkSort(v_a_2784_);
lean_inc(v_a_2780_);
v___x_2786_ = l_Lean_mkArrow(v_a_2780_, v___x_2785_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_a_2787_);
v___x_2789_ = 0;
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Lean_Meta_mkFreshExprMVar(v___x_2788_, v___x_2789_, v___x_2790_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc_n(v_a_2792_, 2);
lean_dec_ref(v___x_2791_);
v___x_2793_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_a_2784_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2782_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_inc_ref(v___x_2796_);
v___x_2797_ = l_Lean_Expr_const___override(v___x_2793_, v___x_2796_);
lean_inc(v_a_2780_);
v___x_2798_ = l_Lean_mkAppB(v___x_2797_, v_a_2780_, v_a_2792_);
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lean_Meta_trySynthInstance(v___x_2798_, v___x_2799_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2887_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2887_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2887_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_a_2801_) == 1)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2883_; 
lean_del_object(v___x_2803_);
v_a_2805_ = lean_ctor_get(v_a_2801_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2801_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2807_ = v_a_2801_;
v_isShared_2808_ = v_isSharedCheck_2883_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v_a_2801_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2883_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2809_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2810_ = l_Lean_Expr_const___override(v___x_2809_, v___x_2796_);
lean_inc_ref(v_expr_2773_);
lean_inc(v_a_2805_);
v___x_2811_ = l_Lean_mkApp4(v___x_2810_, v_a_2780_, v_a_2792_, v_a_2805_, v_expr_2773_);
v___x_2812_ = l_Lean_Meta_expandCoe(v___x_2811_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2874_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2874_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2874_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_fst_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2872_; 
v_fst_2817_ = lean_ctor_get(v_a_2813_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_a_2813_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_a_2813_, 1);
lean_dec(v_unused_2873_);
v___x_2819_ = v_a_2813_;
v_isShared_2820_ = v_isSharedCheck_2872_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_fst_2817_);
lean_dec(v_a_2813_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2872_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2828_; 
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
lean_inc(v_fst_2817_);
v___x_2828_ = lean_infer_type(v_fst_2817_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
v___x_2830_ = lean_whnf(v_a_2829_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; uint8_t v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = l_Lean_Expr_isForall(v_a_2831_);
lean_dec(v_a_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
lean_del_object(v___x_2815_);
lean_del_object(v___x_2807_);
v___x_2833_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2834_ = l_Lean_indentExpr(v_expr_2773_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 7);
lean_ctor_set(v___x_2819_, 1, v___x_2834_);
lean_ctor_set(v___x_2819_, 0, v___x_2833_);
v___x_2836_ = v___x_2819_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v___x_2837_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_indentExpr(v_fst_2817_);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2842_ = l_Lean_indentExpr(v_a_2805_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_MessageData_hint_x27(v___x_2843_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2840_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2845_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
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
else
{
lean_del_object(v___x_2819_);
lean_dec(v_a_2805_);
lean_dec_ref(v_expr_2773_);
goto v___jp_2821_;
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_del_object(v___x_2819_);
lean_dec(v_fst_2817_);
lean_del_object(v___x_2815_);
lean_del_object(v___x_2807_);
lean_dec(v_a_2805_);
lean_dec_ref(v_expr_2773_);
v_a_2856_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2830_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2830_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2819_);
lean_dec(v_fst_2817_);
lean_del_object(v___x_2815_);
lean_del_object(v___x_2807_);
lean_dec(v_a_2805_);
lean_dec_ref(v_expr_2773_);
v_a_2864_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2828_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2828_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
v___jp_2821_:
{
lean_object* v___x_2823_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v_fst_2817_);
v___x_2823_ = v___x_2807_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2817_);
v___x_2823_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2823_);
v___x_2825_ = v___x_2815_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
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
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_del_object(v___x_2807_);
lean_dec(v_a_2805_);
lean_dec_ref(v_expr_2773_);
v_a_2875_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2812_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2812_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
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
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_a_2801_);
lean_dec_ref(v___x_2796_);
lean_dec(v_a_2792_);
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
v___x_2885_ = v___x_2803_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2799_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___x_2796_);
lean_dec(v_a_2792_);
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
v_a_2888_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2800_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2800_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
v_a_2896_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2791_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2791_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2784_);
lean_dec(v_a_2782_);
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
v_a_2904_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2786_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2786_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
v_a_2912_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2783_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2783_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2780_);
lean_dec_ref(v_expr_2773_);
v_a_2920_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2781_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2781_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v_expr_2773_);
v_a_2928_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2779_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2779_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2942_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2951_ = l_Lean_stringToMessageData(v___x_2950_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___x_2961_; 
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
lean_inc_ref(v_expr_2955_);
v___x_2961_ = lean_infer_type(v_expr_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_n(v_a_2962_, 2);
lean_dec_ref(v___x_2961_);
v___x_2963_ = l_Lean_Meta_getLevel(v_a_2962_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc_n(v_a_2966_, 2);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l_Lean_mkSort(v_a_2966_);
v___x_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___x_2969_ = 0;
v___x_2970_ = lean_box(0);
v___x_2971_ = l_Lean_Meta_mkFreshExprMVar(v___x_2968_, v___x_2969_, v___x_2970_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc_n(v_a_2972_, 2);
lean_dec_ref(v___x_2971_);
v___x_2973_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_a_2966_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2964_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
lean_inc_ref(v___x_2976_);
v___x_2977_ = l_Lean_Expr_const___override(v___x_2973_, v___x_2976_);
lean_inc(v_a_2962_);
v___x_2978_ = l_Lean_mkAppB(v___x_2977_, v_a_2962_, v_a_2972_);
v___x_2979_ = lean_box(0);
v___x_2980_ = l_Lean_Meta_trySynthInstance(v___x_2978_, v___x_2979_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3067_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_3067_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3067_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
if (lean_obj_tag(v_a_2981_) == 1)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_2983_);
v_a_2985_ = lean_ctor_get(v_a_2981_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_a_2981_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_2987_ = v_a_2981_;
v_isShared_2988_ = v_isSharedCheck_3063_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v_a_2981_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3063_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2989_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2990_ = l_Lean_Expr_const___override(v___x_2989_, v___x_2976_);
lean_inc_ref(v_expr_2955_);
lean_inc(v_a_2985_);
v___x_2991_ = l_Lean_mkApp4(v___x_2990_, v_a_2962_, v_a_2972_, v_a_2985_, v_expr_2955_);
v___x_2992_ = l_Lean_Meta_expandCoe(v___x_2991_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3054_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3054_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3054_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v_fst_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3052_; 
v_fst_2997_ = lean_ctor_get(v_a_2993_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_2993_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v_a_2993_, 1);
lean_dec(v_unused_3053_);
v___x_2999_ = v_a_2993_;
v_isShared_3000_ = v_isSharedCheck_3052_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_fst_2997_);
lean_dec(v_a_2993_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3052_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3008_; 
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
lean_inc(v_fst_2997_);
v___x_3008_ = lean_infer_type(v_fst_2997_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3008_);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
v___x_3010_ = lean_whnf(v_a_3009_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = l_Lean_Expr_isSort(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
v___x_3013_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3014_ = l_Lean_indentExpr(v_expr_2955_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 7);
lean_ctor_set(v___x_2999_, 1, v___x_3014_);
lean_ctor_set(v___x_2999_, 0, v___x_3013_);
v___x_3016_ = v___x_2999_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
v___x_3017_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_indentExpr(v_fst_2997_);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3022_ = l_Lean_indentExpr(v_a_2985_);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = l_Lean_MessageData_hint_x27(v___x_3023_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3020_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3025_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
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
else
{
lean_del_object(v___x_2999_);
lean_dec(v_a_2985_);
lean_dec_ref(v_expr_2955_);
goto v___jp_3001_;
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_a_2985_);
lean_dec_ref(v_expr_2955_);
v_a_3036_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3010_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3010_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_del_object(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_a_2985_);
lean_dec_ref(v_expr_2955_);
v_a_3044_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3008_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3008_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
v___jp_3001_:
{
lean_object* v___x_3003_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v_fst_2997_);
v___x_3003_ = v___x_2987_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_fst_2997_);
v___x_3003_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_3003_);
v___x_3005_ = v___x_2995_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
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
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_2987_);
lean_dec(v_a_2985_);
lean_dec_ref(v_expr_2955_);
v_a_3055_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2992_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2992_);
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
}
else
{
lean_object* v___x_3065_; 
lean_dec(v_a_2981_);
lean_dec_ref(v___x_2976_);
lean_dec(v_a_2972_);
lean_dec(v_a_2962_);
lean_dec_ref(v_expr_2955_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2979_);
v___x_3065_ = v___x_2983_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_2979_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___x_2976_);
lean_dec(v_a_2972_);
lean_dec(v_a_2962_);
lean_dec_ref(v_expr_2955_);
v_a_3068_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2980_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2980_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_2966_);
lean_dec(v_a_2964_);
lean_dec(v_a_2962_);
lean_dec_ref(v_expr_2955_);
v_a_3076_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2971_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2971_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_2964_);
lean_dec(v_a_2962_);
lean_dec_ref(v_expr_2955_);
v_a_3084_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2965_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2965_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_2962_);
lean_dec_ref(v_expr_2955_);
v_a_3092_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2963_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2963_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec_ref(v_expr_2955_);
v_a_3100_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_2961_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_2961_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3115_, lean_object* v___y_3116_){
_start:
{
uint8_t v___x_3118_; 
v___x_3118_ = l_Lean_Expr_hasMVar(v_e_3115_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_e_3115_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v_mctx_3121_; lean_object* v___x_3122_; lean_object* v_fst_3123_; lean_object* v_snd_3124_; lean_object* v___x_3125_; lean_object* v_cache_3126_; lean_object* v_zetaDeltaFVarIds_3127_; lean_object* v_postponed_3128_; lean_object* v_diag_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3138_; 
v___x_3120_ = lean_st_ref_get(v___y_3116_);
v_mctx_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc_ref(v_mctx_3121_);
lean_dec(v___x_3120_);
v___x_3122_ = l_Lean_instantiateMVarsCore(v_mctx_3121_, v_e_3115_);
v_fst_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_fst_3123_);
v_snd_3124_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_snd_3124_);
lean_dec_ref(v___x_3122_);
v___x_3125_ = lean_st_ref_take(v___y_3116_);
v_cache_3126_ = lean_ctor_get(v___x_3125_, 1);
v_zetaDeltaFVarIds_3127_ = lean_ctor_get(v___x_3125_, 2);
v_postponed_3128_ = lean_ctor_get(v___x_3125_, 3);
v_diag_3129_ = lean_ctor_get(v___x_3125_, 4);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3125_, 0);
lean_dec(v_unused_3139_);
v___x_3131_ = v___x_3125_;
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_diag_3129_);
lean_inc(v_postponed_3128_);
lean_inc(v_zetaDeltaFVarIds_3127_);
lean_inc(v_cache_3126_);
lean_dec(v___x_3125_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_snd_3124_);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_snd_3124_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_cache_3126_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_zetaDeltaFVarIds_3127_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_postponed_3128_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_diag_3129_);
v___x_3134_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_st_ref_set(v___y_3116_, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_fst_3123_);
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3140_, v___y_3141_);
lean_dec(v___y_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3144_, v___y_3146_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3157_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3158_; uint64_t v___x_3159_; 
v___x_3158_ = 2;
v___x_3159_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3166_; uint8_t v_foApprox_3167_; uint8_t v_ctxApprox_3168_; uint8_t v_quasiPatternApprox_3169_; uint8_t v_constApprox_3170_; uint8_t v_isDefEqStuckEx_3171_; uint8_t v_unificationHints_3172_; uint8_t v_proofIrrelevance_3173_; uint8_t v_assignSyntheticOpaque_3174_; uint8_t v_offsetCnstrs_3175_; uint8_t v_etaStruct_3176_; uint8_t v_univApprox_3177_; uint8_t v_iota_3178_; uint8_t v_beta_3179_; uint8_t v_proj_3180_; uint8_t v_zeta_3181_; uint8_t v_zetaDelta_3182_; uint8_t v_zetaUnused_3183_; uint8_t v_zetaHave_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3249_; 
v___x_3166_ = l_Lean_Meta_Context_config(v_a_3161_);
v_foApprox_3167_ = lean_ctor_get_uint8(v___x_3166_, 0);
v_ctxApprox_3168_ = lean_ctor_get_uint8(v___x_3166_, 1);
v_quasiPatternApprox_3169_ = lean_ctor_get_uint8(v___x_3166_, 2);
v_constApprox_3170_ = lean_ctor_get_uint8(v___x_3166_, 3);
v_isDefEqStuckEx_3171_ = lean_ctor_get_uint8(v___x_3166_, 4);
v_unificationHints_3172_ = lean_ctor_get_uint8(v___x_3166_, 5);
v_proofIrrelevance_3173_ = lean_ctor_get_uint8(v___x_3166_, 6);
v_assignSyntheticOpaque_3174_ = lean_ctor_get_uint8(v___x_3166_, 7);
v_offsetCnstrs_3175_ = lean_ctor_get_uint8(v___x_3166_, 8);
v_etaStruct_3176_ = lean_ctor_get_uint8(v___x_3166_, 10);
v_univApprox_3177_ = lean_ctor_get_uint8(v___x_3166_, 11);
v_iota_3178_ = lean_ctor_get_uint8(v___x_3166_, 12);
v_beta_3179_ = lean_ctor_get_uint8(v___x_3166_, 13);
v_proj_3180_ = lean_ctor_get_uint8(v___x_3166_, 14);
v_zeta_3181_ = lean_ctor_get_uint8(v___x_3166_, 15);
v_zetaDelta_3182_ = lean_ctor_get_uint8(v___x_3166_, 16);
v_zetaUnused_3183_ = lean_ctor_get_uint8(v___x_3166_, 17);
v_zetaHave_3184_ = lean_ctor_get_uint8(v___x_3166_, 18);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3186_ = v___x_3166_;
v_isShared_3187_ = v_isSharedCheck_3249_;
goto v_resetjp_3185_;
}
else
{
lean_dec(v___x_3166_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3249_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
uint8_t v_trackZetaDelta_3188_; lean_object* v_zetaDeltaSet_3189_; lean_object* v_lctx_3190_; lean_object* v_localInstances_3191_; lean_object* v_defEqCtx_x3f_3192_; lean_object* v_synthPendingDepth_3193_; lean_object* v_canUnfold_x3f_3194_; uint8_t v_univApprox_3195_; uint8_t v_inTypeClassResolution_3196_; uint8_t v_cacheInferType_3197_; uint8_t v___x_3198_; lean_object* v_config_3200_; 
v_trackZetaDelta_3188_ = lean_ctor_get_uint8(v_a_3161_, sizeof(void*)*7);
v_zetaDeltaSet_3189_ = lean_ctor_get(v_a_3161_, 1);
v_lctx_3190_ = lean_ctor_get(v_a_3161_, 2);
v_localInstances_3191_ = lean_ctor_get(v_a_3161_, 3);
v_defEqCtx_x3f_3192_ = lean_ctor_get(v_a_3161_, 4);
v_synthPendingDepth_3193_ = lean_ctor_get(v_a_3161_, 5);
v_canUnfold_x3f_3194_ = lean_ctor_get(v_a_3161_, 6);
v_univApprox_3195_ = lean_ctor_get_uint8(v_a_3161_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3196_ = lean_ctor_get_uint8(v_a_3161_, sizeof(void*)*7 + 2);
v_cacheInferType_3197_ = lean_ctor_get_uint8(v_a_3161_, sizeof(void*)*7 + 3);
v___x_3198_ = 2;
if (v_isShared_3187_ == 0)
{
v_config_3200_ = v___x_3186_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 0, v_foApprox_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 1, v_ctxApprox_3168_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 2, v_quasiPatternApprox_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 3, v_constApprox_3170_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 4, v_isDefEqStuckEx_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 5, v_unificationHints_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 6, v_proofIrrelevance_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 7, v_assignSyntheticOpaque_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 8, v_offsetCnstrs_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 10, v_etaStruct_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 11, v_univApprox_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 12, v_iota_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 13, v_beta_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 14, v_proj_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 15, v_zeta_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 16, v_zetaDelta_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 17, v_zetaUnused_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3248_, 18, v_zetaHave_3184_);
v_config_3200_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
uint64_t v___x_3201_; uint64_t v___x_3202_; uint64_t v___x_3203_; uint64_t v___x_3204_; uint64_t v___x_3205_; uint64_t v_key_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_ctor_set_uint8(v_config_3200_, 9, v___x_3198_);
v___x_3201_ = l_Lean_Meta_Context_configKey(v_a_3161_);
v___x_3202_ = 2ULL;
v___x_3203_ = lean_uint64_shift_right(v___x_3201_, v___x_3202_);
v___x_3204_ = lean_uint64_shift_left(v___x_3203_, v___x_3202_);
v___x_3205_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3206_ = lean_uint64_lor(v___x_3204_, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3207_, 0, v_config_3200_);
lean_ctor_set_uint64(v___x_3207_, sizeof(void*)*1, v_key_3206_);
lean_inc(v_canUnfold_x3f_3194_);
lean_inc(v_synthPendingDepth_3193_);
lean_inc(v_defEqCtx_x3f_3192_);
lean_inc_ref(v_localInstances_3191_);
lean_inc_ref(v_lctx_3190_);
lean_inc(v_zetaDeltaSet_3189_);
v___x_3208_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v_zetaDeltaSet_3189_);
lean_ctor_set(v___x_3208_, 2, v_lctx_3190_);
lean_ctor_set(v___x_3208_, 3, v_localInstances_3191_);
lean_ctor_set(v___x_3208_, 4, v_defEqCtx_x3f_3192_);
lean_ctor_set(v___x_3208_, 5, v_synthPendingDepth_3193_);
lean_ctor_set(v___x_3208_, 6, v_canUnfold_x3f_3194_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*7, v_trackZetaDelta_3188_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*7 + 1, v_univApprox_3195_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3196_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*7 + 3, v_cacheInferType_3197_);
lean_inc(v_a_3164_);
lean_inc_ref(v_a_3163_);
lean_inc(v_a_3162_);
v___x_3209_ = lean_whnf(v_type_3160_, v___x_3208_, v_a_3162_, v_a_3163_, v_a_3164_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3239_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3239_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3239_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
if (lean_obj_tag(v_a_3210_) == 5)
{
lean_object* v_fn_3214_; lean_object* v_arg_3215_; lean_object* v___x_3216_; lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3212_);
v_fn_3214_ = lean_ctor_get(v_a_3210_, 0);
lean_inc_ref(v_fn_3214_);
v_arg_3215_ = lean_ctor_get(v_a_3210_, 1);
lean_inc_ref(v_arg_3215_);
lean_dec_ref(v_a_3210_);
v___x_3216_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3214_, v_a_3162_);
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3234_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3234_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3233_; 
v___x_3221_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3215_, v_a_3162_);
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_a_3217_);
lean_ctor_set(v___x_3226_, 1, v_a_3222_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 1);
lean_ctor_set(v___x_3219_, 0, v___x_3226_);
v___x_3228_ = v___x_3219_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3230_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3228_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_dec(v_a_3210_);
v___x_3235_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3235_);
v___x_3237_ = v___x_3212_;
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
v_a_3240_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3209_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3209_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Meta_isTypeApp_x3f(v_type_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Meta_isTypeApp_x3f(v_type_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3299_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3299_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3299_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
if (lean_obj_tag(v_a_3264_) == 1)
{
lean_object* v_val_3268_; lean_object* v_fst_3269_; lean_object* v___x_3270_; 
lean_del_object(v___x_3266_);
v_val_3268_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_val_3268_);
lean_dec_ref(v_a_3264_);
v_fst_3269_ = lean_ctor_get(v_val_3268_, 0);
lean_inc(v_fst_3269_);
lean_dec(v_val_3268_);
v___x_3270_ = l_Lean_Meta_isMonad_x3f(v_fst_3269_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3285_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3285_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3285_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
if (lean_obj_tag(v_a_3271_) == 0)
{
uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3275_ = 0;
v___x_3276_ = lean_box(v___x_3275_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
else
{
uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec_ref(v_a_3271_);
v___x_3280_ = 1;
v___x_3281_ = lean_box(v___x_3280_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3281_);
v___x_3283_ = v___x_3273_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3270_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3270_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_dec(v_a_3264_);
v___x_3294_ = 0;
v___x_3295_ = lean_box(v___x_3294_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3295_);
v___x_3297_ = v___x_3266_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_a_3300_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3263_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3263_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_isMonadApp(v_type_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3315_, lean_object* v_opt_3316_){
_start:
{
lean_object* v_name_3317_; lean_object* v_defValue_3318_; lean_object* v_map_3319_; lean_object* v___x_3320_; 
v_name_3317_ = lean_ctor_get(v_opt_3316_, 0);
v_defValue_3318_ = lean_ctor_get(v_opt_3316_, 1);
v_map_3319_ = lean_ctor_get(v_opts_3315_, 0);
v___x_3320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3319_, v_name_3317_);
if (lean_obj_tag(v___x_3320_) == 0)
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_unbox(v_defValue_3318_);
return v___x_3321_;
}
else
{
lean_object* v_val_3322_; 
v_val_3322_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3322_);
lean_dec_ref(v___x_3320_);
if (lean_obj_tag(v_val_3322_) == 1)
{
uint8_t v_v_3323_; 
v_v_3323_ = lean_ctor_get_uint8(v_val_3322_, 0);
lean_dec_ref(v_val_3322_);
return v_v_3323_;
}
else
{
uint8_t v___x_3324_; 
lean_dec(v_val_3322_);
v___x_3324_ = lean_unbox(v_defValue_3318_);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3325_, lean_object* v_opt_3326_){
_start:
{
uint8_t v_res_3327_; lean_object* v_r_3328_; 
v_res_3327_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3325_, v_opt_3326_);
lean_dec_ref(v_opt_3326_);
lean_dec_ref(v_opts_3325_);
v_r_3328_ = lean_box(v_res_3327_);
return v_r_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec_ref(v_x_3339_);
return v_res_3345_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = l_Lean_mkBVar(v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3368_, lean_object* v_expectedType_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___y_3376_; uint8_t v___y_3377_; lean_object* v_a_3382_; lean_object* v___y_3386_; lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3800_; 
v___x_3396_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3369_, v_a_3371_);
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3800_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3800_;
goto v_resetjp_3398_;
}
v___jp_3375_:
{
if (v___y_3377_ == 0)
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
lean_dec_ref(v___y_3376_);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
else
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___y_3376_);
return v___x_3380_;
}
}
v___jp_3381_:
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Lean_Exception_isInterrupt(v_a_3382_);
if (v___x_3383_ == 0)
{
uint8_t v___x_3384_; 
lean_inc_ref(v_a_3382_);
v___x_3384_ = l_Lean_Exception_isRuntime(v_a_3382_);
v___y_3376_ = v_a_3382_;
v___y_3377_ = v___x_3384_;
goto v___jp_3375_;
}
else
{
v___y_3376_ = v_a_3382_;
v___y_3377_ = v___x_3383_;
goto v___jp_3375_;
}
}
v___jp_3385_:
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3395_; 
v_a_3387_ = lean_ctor_get(v___y_3386_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___y_3386_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3389_ = v___y_3386_;
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___y_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3395_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_a_3391_; lean_object* v___x_3393_; 
v_a_3391_ = lean_ctor_get(v_a_3387_, 0);
lean_inc(v_a_3391_);
lean_dec(v_a_3387_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_a_3391_);
v___x_3393_ = v___x_3389_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; 
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
lean_inc_ref(v_e_3368_);
v___x_3401_ = lean_infer_type(v_e_3368_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3791_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3402_, v_a_3371_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3791_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3791_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; 
lean_inc(v_a_3397_);
v___x_3408_ = l_Lean_Meta_isTypeApp_x3f(v_a_3397_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3782_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3782_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3782_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
if (lean_obj_tag(v_a_3409_) == 1)
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3777_; 
lean_del_object(v___x_3411_);
v_val_3413_ = lean_ctor_get(v_a_3409_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3409_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3415_ = v_a_3409_;
v_isShared_3416_ = v_isSharedCheck_3777_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v_a_3409_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3777_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_fst_3417_; lean_object* v_snd_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3776_; 
v_fst_3417_ = lean_ctor_get(v_val_3413_, 0);
v_snd_3418_ = lean_ctor_get(v_val_3413_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_val_3413_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3420_ = v_val_3413_;
v_isShared_3421_ = v_isSharedCheck_3776_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_snd_3418_);
lean_inc(v_fst_3417_);
lean_dec(v_val_3413_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3776_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; 
lean_inc(v_a_3404_);
v___x_3422_ = l_Lean_Meta_isTypeApp_x3f(v_a_3404_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3767_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3767_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3767_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
if (lean_obj_tag(v_a_3423_) == 1)
{
lean_object* v_val_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3425_);
v_val_3427_ = lean_ctor_get(v_a_3423_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3423_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3429_ = v_a_3423_;
v_isShared_3430_ = v_isSharedCheck_3762_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_val_3427_);
lean_dec(v_a_3423_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3762_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3761_; 
v_fst_3431_ = lean_ctor_get(v_val_3427_, 0);
v_snd_3432_ = lean_ctor_get(v_val_3427_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_val_3427_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3434_ = v_val_3427_;
v_isShared_3435_ = v_isSharedCheck_3761_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_val_3427_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3761_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Meta_saveState___redArg(v_a_3371_, v_a_3373_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref(v___x_3436_);
lean_inc(v_fst_3417_);
lean_inc(v_fst_3431_);
v___x_3438_ = l_Lean_Meta_isExprDefEq(v_fst_3431_, v_fst_3417_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3744_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3744_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3744_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_unbox(v_a_3439_);
lean_dec(v_a_3439_);
if (v___x_3443_ == 0)
{
lean_object* v_options_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
lean_dec(v_a_3437_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3399_);
v_options_3444_ = lean_ctor_get(v_a_3372_, 2);
v___x_3445_ = l_Lean_Meta_autoLift;
v___x_3446_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3447_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3447_);
v___x_3449_ = v___x_3441_;
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
else
{
lean_object* v___x_3451_; 
lean_del_object(v___x_3441_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
lean_inc(v_fst_3431_);
v___x_3451_ = lean_infer_type(v_fst_3431_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref(v___x_3451_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
v___x_3453_ = lean_whnf(v_a_3452_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
if (lean_obj_tag(v_a_3454_) == 7)
{
lean_object* v_binderType_3455_; 
v_binderType_3455_ = lean_ctor_get(v_a_3454_, 1);
if (lean_obj_tag(v_binderType_3455_) == 3)
{
lean_object* v_body_3456_; 
v_body_3456_ = lean_ctor_get(v_a_3454_, 2);
if (lean_obj_tag(v_body_3456_) == 3)
{
lean_object* v_u_3457_; lean_object* v_u_3458_; lean_object* v___x_3459_; 
lean_inc_ref(v_body_3456_);
lean_inc_ref(v_binderType_3455_);
lean_dec_ref(v_a_3454_);
v_u_3457_ = lean_ctor_get(v_binderType_3455_, 0);
lean_inc(v_u_3457_);
lean_dec_ref(v_binderType_3455_);
v_u_3458_ = lean_ctor_get(v_body_3456_, 0);
lean_inc(v_u_3458_);
lean_dec_ref(v_body_3456_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
lean_inc(v_fst_3417_);
v___x_3459_ = lean_infer_type(v_fst_3417_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
v___x_3461_ = lean_whnf(v_a_3460_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
if (lean_obj_tag(v_a_3462_) == 7)
{
lean_object* v_binderType_3463_; 
v_binderType_3463_ = lean_ctor_get(v_a_3462_, 1);
if (lean_obj_tag(v_binderType_3463_) == 3)
{
lean_object* v_body_3464_; 
v_body_3464_ = lean_ctor_get(v_a_3462_, 2);
if (lean_obj_tag(v_body_3464_) == 3)
{
lean_object* v_u_3465_; lean_object* v_u_3466_; lean_object* v___x_3467_; 
lean_inc_ref(v_body_3464_);
lean_inc_ref(v_binderType_3463_);
lean_dec_ref(v_a_3462_);
v_u_3465_ = lean_ctor_get(v_binderType_3463_, 0);
lean_inc(v_u_3465_);
lean_dec_ref(v_binderType_3463_);
v_u_3466_ = lean_ctor_get(v_body_3464_, 0);
lean_inc(v_u_3466_);
lean_dec_ref(v_body_3464_);
v___x_3467_ = l_Lean_Meta_decLevel(v_u_3457_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = l_Lean_Meta_decLevel(v_u_3465_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref(v___x_3469_);
lean_inc(v_a_3468_);
v___x_3471_ = l_Lean_Meta_isLevelDefEq(v_a_3468_, v_a_3470_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3636_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3636_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3636_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_unbox(v_a_3472_);
lean_dec(v_a_3472_);
if (v___x_3476_ == 1)
{
lean_object* v___x_3477_; 
lean_del_object(v___x_3474_);
v___x_3477_ = l_Lean_Meta_decLevel(v_u_3458_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = l_Lean_Meta_decLevel(v_u_3466_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3482_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 1, v___x_3482_);
lean_ctor_set(v___x_3434_, 0, v_a_3480_);
v___x_3484_ = v___x_3434_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3480_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3486_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set_tag(v___x_3420_, 1);
lean_ctor_set(v___x_3420_, 1, v___x_3484_);
lean_ctor_set(v___x_3420_, 0, v_a_3478_);
v___x_3486_ = v___x_3420_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3478_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3468_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_Expr_const___override(v___x_3481_, v___x_3487_);
v___x_3489_ = lean_unsigned_to_nat(2u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
lean_inc(v_fst_3431_);
v___x_3491_ = lean_array_push(v___x_3490_, v_fst_3431_);
lean_inc(v_fst_3417_);
v___x_3492_ = lean_array_push(v___x_3491_, v_fst_3417_);
v___x_3493_ = l_Lean_mkAppN(v___x_3488_, v___x_3492_);
lean_dec_ref(v___x_3492_);
v___x_3494_ = lean_box(0);
v___x_3495_ = l_Lean_Meta_trySynthInstance(v___x_3493_, v___x_3494_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3626_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3626_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3626_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
lean_del_object(v___x_3498_);
v_a_3500_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3500_);
lean_dec_ref(v_a_3496_);
lean_inc(v_snd_3432_);
v___x_3501_ = l_Lean_Meta_getDecLevel(v_snd_3432_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = l_Lean_Meta_getDecLevel(v_a_3404_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
lean_inc(v_a_3397_);
v___x_3505_ = l_Lean_Meta_getDecLevel(v_a_3397_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_a_3506_);
lean_ctor_set(v___x_3508_, 1, v___x_3482_);
v___x_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3509_, 0, v_a_3504_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_a_3502_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
lean_inc_ref(v___x_3510_);
v___x_3511_ = l_Lean_mkConst(v___x_3507_, v___x_3510_);
v___x_3512_ = lean_unsigned_to_nat(5u);
v___x_3513_ = lean_mk_empty_array_with_capacity(v___x_3512_);
lean_inc(v_fst_3431_);
v___x_3514_ = lean_array_push(v___x_3513_, v_fst_3431_);
lean_inc(v_fst_3417_);
v___x_3515_ = lean_array_push(v___x_3514_, v_fst_3417_);
lean_inc(v_a_3500_);
v___x_3516_ = lean_array_push(v___x_3515_, v_a_3500_);
lean_inc(v_snd_3432_);
v___x_3517_ = lean_array_push(v___x_3516_, v_snd_3432_);
lean_inc_ref(v_e_3368_);
v___x_3518_ = lean_array_push(v___x_3517_, v_e_3368_);
v___x_3519_ = l_Lean_mkAppN(v___x_3511_, v___x_3518_);
lean_dec_ref(v___x_3518_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
lean_inc_ref(v___x_3519_);
v___x_3520_ = lean_infer_type(v___x_3519_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
lean_inc(v_a_3397_);
v___x_3522_ = l_Lean_Meta_isExprDefEq(v_a_3397_, v_a_3521_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3617_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3617_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3617_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_unbox(v_a_3523_);
lean_dec(v_a_3523_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_del_object(v___x_3525_);
lean_dec_ref(v___x_3519_);
lean_del_object(v___x_3429_);
lean_inc(v_fst_3417_);
v___x_3528_ = l_Lean_Meta_isMonad_x3f(v_fst_3417_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3609_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3609_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3609_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
if (lean_obj_tag(v_a_3529_) == 1)
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3605_; 
lean_del_object(v___x_3531_);
v_val_3533_ = lean_ctor_get(v_a_3529_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_a_3529_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3535_ = v_a_3529_;
v_isShared_3536_ = v_isSharedCheck_3605_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v_a_3529_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3605_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; 
lean_inc(v_snd_3432_);
v___x_3537_ = l_Lean_Meta_getLevel(v_snd_3432_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3537_);
lean_inc(v_snd_3418_);
v___x_3539_ = l_Lean_Meta_getLevel(v_snd_3418_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3542_ = 0;
v___x_3543_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_a_3540_);
lean_ctor_set(v___x_3544_, 1, v___x_3482_);
v___x_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_a_3538_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Lean_mkConst(v___x_3543_, v___x_3545_);
v___x_3547_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3548_ = lean_unsigned_to_nat(3u);
v___x_3549_ = lean_mk_empty_array_with_capacity(v___x_3548_);
lean_inc_n(v_snd_3432_, 2);
v___x_3550_ = lean_array_push(v___x_3549_, v_snd_3432_);
v___x_3551_ = lean_array_push(v___x_3550_, v___x_3547_);
lean_inc(v_snd_3418_);
v___x_3552_ = lean_array_push(v___x_3551_, v_snd_3418_);
v___x_3553_ = l_Lean_mkAppN(v___x_3546_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = l_Lean_mkForall(v___x_3541_, v___x_3542_, v_snd_3432_, v___x_3553_);
v___x_3555_ = l_Lean_Meta_trySynthInstance(v___x_3554_, v___x_3494_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3601_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3601_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3601_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
if (lean_obj_tag(v_a_3556_) == 1)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_del_object(v___x_3558_);
v_a_3560_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_a_3560_);
lean_dec_ref(v_a_3556_);
v___x_3561_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3562_ = l_Lean_mkConst(v___x_3561_, v___x_3510_);
v___x_3563_ = lean_unsigned_to_nat(8u);
v___x_3564_ = lean_mk_empty_array_with_capacity(v___x_3563_);
v___x_3565_ = lean_array_push(v___x_3564_, v_fst_3431_);
v___x_3566_ = lean_array_push(v___x_3565_, v_fst_3417_);
v___x_3567_ = lean_array_push(v___x_3566_, v_snd_3432_);
v___x_3568_ = lean_array_push(v___x_3567_, v_snd_3418_);
v___x_3569_ = lean_array_push(v___x_3568_, v_a_3500_);
v___x_3570_ = lean_array_push(v___x_3569_, v_a_3560_);
v___x_3571_ = lean_array_push(v___x_3570_, v_val_3533_);
v___x_3572_ = lean_array_push(v___x_3571_, v_e_3368_);
v___x_3573_ = l_Lean_mkAppN(v___x_3562_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = l_Lean_Meta_expandCoe(v___x_3573_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_fst_3576_; lean_object* v___x_3577_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v_fst_3576_ = lean_ctor_get(v_a_3575_, 0);
lean_inc_n(v_fst_3576_, 2);
lean_dec(v_a_3575_);
lean_inc(v_a_3373_);
lean_inc_ref(v_a_3372_);
lean_inc(v_a_3371_);
lean_inc_ref(v_a_3370_);
v___x_3577_ = lean_infer_type(v_fst_3576_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref(v___x_3577_);
v___x_3579_ = l_Lean_Meta_isExprDefEq(v_a_3397_, v_a_3578_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3594_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3594_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3594_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
uint8_t v___x_3584_; 
v___x_3584_ = lean_unbox(v_a_3580_);
lean_dec(v_a_3580_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3586_; 
lean_dec(v_fst_3576_);
lean_del_object(v___x_3535_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3494_);
v___x_3586_ = v___x_3582_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3494_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
else
{
lean_object* v___x_3589_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_fst_3576_);
v___x_3589_ = v___x_3535_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_fst_3576_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3589_);
v___x_3591_ = v___x_3582_;
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
}
else
{
lean_object* v_a_3595_; 
lean_dec(v_fst_3576_);
lean_del_object(v___x_3535_);
v_a_3595_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3579_);
v_a_3382_ = v_a_3595_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3596_; 
lean_dec(v_fst_3576_);
lean_del_object(v___x_3535_);
lean_dec(v_a_3397_);
v_a_3596_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3577_);
v_a_3382_ = v_a_3596_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3597_; 
lean_del_object(v___x_3535_);
lean_dec(v_a_3397_);
v_a_3597_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3574_);
v_a_3382_ = v_a_3597_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3599_; 
lean_dec(v_a_3556_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3494_);
v___x_3599_ = v___x_3558_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3494_);
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
lean_object* v_a_3602_; 
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3602_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3602_);
lean_dec_ref(v___x_3555_);
v_a_3382_ = v_a_3602_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3603_; 
lean_dec(v_a_3538_);
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3603_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3603_);
lean_dec_ref(v___x_3539_);
v_a_3382_ = v_a_3603_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3604_; 
lean_del_object(v___x_3535_);
lean_dec(v_val_3533_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3604_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3537_);
v_a_3382_ = v_a_3604_;
goto v___jp_3381_;
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v_a_3529_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3494_);
v___x_3607_ = v___x_3531_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3494_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_a_3610_; 
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3610_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3528_);
v_a_3382_ = v_a_3610_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3612_; 
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3519_);
v___x_3612_ = v___x_3429_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3519_);
v___x_3612_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3612_);
v___x_3614_ = v___x_3525_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
else
{
lean_object* v_a_3618_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3618_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3522_);
v_a_3382_ = v_a_3618_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3619_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref(v___x_3510_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3619_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v___x_3520_);
v_a_3382_ = v_a_3619_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3620_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3502_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3620_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3505_);
v_a_3382_ = v_a_3620_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3621_; 
lean_dec(v_a_3502_);
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3621_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3503_);
v_a_3382_ = v_a_3621_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3622_; 
lean_dec(v_a_3500_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3622_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3501_);
v_a_3382_ = v_a_3622_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3624_; 
lean_dec(v_a_3496_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3494_);
v___x_3624_ = v___x_3498_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3494_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; 
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3627_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3627_);
lean_dec_ref(v___x_3495_);
v_a_3382_ = v_a_3627_;
goto v___jp_3381_;
}
}
}
}
else
{
lean_object* v_a_3630_; 
lean_dec(v_a_3478_);
lean_dec(v_a_3468_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3630_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3479_);
v_a_3382_ = v_a_3630_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3631_; 
lean_dec(v_a_3468_);
lean_dec(v_u_3466_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3631_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3631_);
lean_dec_ref(v___x_3477_);
v_a_3382_ = v_a_3631_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
lean_dec(v_a_3468_);
lean_dec(v_u_3466_);
lean_dec(v_u_3458_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3632_ = lean_box(0);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3632_);
v___x_3634_ = v___x_3474_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v_a_3637_; 
lean_dec(v_a_3468_);
lean_dec(v_u_3466_);
lean_dec(v_u_3458_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3637_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___x_3471_);
v_a_3382_ = v_a_3637_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3638_; 
lean_dec(v_a_3468_);
lean_dec(v_u_3466_);
lean_dec(v_u_3458_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3638_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3469_);
v_a_3382_ = v_a_3638_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3639_; 
lean_dec(v_u_3466_);
lean_dec(v_u_3465_);
lean_dec(v_u_3458_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3639_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3467_);
v_a_3382_ = v_a_3639_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3640_; 
lean_dec(v_u_3458_);
lean_dec(v_u_3457_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3640_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec_ref(v_a_3462_);
v___y_3386_ = v___x_3640_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3641_; 
lean_dec(v_u_3458_);
lean_dec(v_u_3457_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3641_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec_ref(v_a_3462_);
v___y_3386_ = v___x_3641_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3642_; 
lean_dec(v_u_3458_);
lean_dec(v_u_3457_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3642_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3462_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec(v_a_3462_);
v___y_3386_ = v___x_3642_;
goto v___jp_3385_;
}
}
else
{
lean_object* v_a_3643_; 
lean_dec(v_u_3458_);
lean_dec(v_u_3457_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3643_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3461_);
v_a_3382_ = v_a_3643_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3644_; 
lean_dec(v_u_3458_);
lean_dec(v_u_3457_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3644_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3459_);
v_a_3382_ = v_a_3644_;
goto v___jp_3381_;
}
}
else
{
lean_object* v___x_3645_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3645_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec_ref(v_a_3454_);
v___y_3386_ = v___x_3645_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3646_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3646_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec_ref(v_a_3454_);
v___y_3386_ = v___x_3646_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3647_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3647_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3454_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec(v_a_3454_);
v___y_3386_ = v___x_3647_;
goto v___jp_3385_;
}
}
else
{
lean_object* v_a_3648_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3648_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3648_);
lean_dec_ref(v___x_3453_);
v_a_3382_ = v_a_3648_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3649_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3649_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3451_);
v_a_3382_ = v_a_3649_;
goto v___jp_3381_;
}
}
}
else
{
lean_object* v___x_3650_; 
lean_del_object(v___x_3441_);
lean_del_object(v___x_3434_);
lean_del_object(v___x_3420_);
lean_dec(v_a_3404_);
lean_dec(v_a_3397_);
v___x_3650_ = l_Lean_Meta_isMonad_x3f(v_fst_3417_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3743_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3743_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3743_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
if (lean_obj_tag(v_a_3651_) == 1)
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3655_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v_fst_3431_);
v___x_3657_ = v___x_3429_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_fst_3431_);
v___x_3657_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3659_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_snd_3432_);
v___x_3659_ = v___x_3415_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_snd_3432_);
v___x_3659_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 1);
lean_ctor_set(v___x_3406_, 0, v_snd_3418_);
v___x_3661_ = v___x_3406_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_snd_3418_);
v___x_3661_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___y_3664_; uint8_t v___y_3665_; lean_object* v_a_3687_; lean_object* v___x_3691_; 
v___x_3662_ = lean_box(0);
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 1);
lean_ctor_set(v___x_3399_, 0, v_e_3368_);
v___x_3691_ = v___x_3399_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_e_3368_);
v___x_3691_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3690_;
}
v___jp_3663_:
{
if (v___y_3665_ == 0)
{
lean_object* v___x_3666_; 
lean_dec_ref(v___y_3664_);
lean_del_object(v___x_3653_);
v___x_3666_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3437_, v_a_3371_, v_a_3373_);
lean_dec(v_a_3437_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___x_3666_, 0);
lean_dec(v_unused_3674_);
v___x_3668_ = v___x_3666_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v___x_3666_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3662_);
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3662_);
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
v_a_3675_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3666_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3666_);
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
else
{
lean_object* v___x_3684_; 
lean_dec(v_a_3437_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v___y_3664_);
v___x_3684_ = v___x_3653_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___y_3664_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
v___jp_3686_:
{
uint8_t v___x_3688_; 
v___x_3688_ = l_Lean_Exception_isInterrupt(v_a_3687_);
if (v___x_3688_ == 0)
{
uint8_t v___x_3689_; 
lean_inc_ref(v_a_3687_);
v___x_3689_ = l_Lean_Exception_isRuntime(v_a_3687_);
v___y_3664_ = v_a_3687_;
v___y_3665_ = v___x_3689_;
goto v___jp_3663_;
}
else
{
v___y_3664_ = v_a_3687_;
v___y_3665_ = v___x_3688_;
goto v___jp_3663_;
}
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3692_ = lean_unsigned_to_nat(6u);
v___x_3693_ = lean_mk_empty_array_with_capacity(v___x_3692_);
v___x_3694_ = lean_array_push(v___x_3693_, v___x_3657_);
v___x_3695_ = lean_array_push(v___x_3694_, v___x_3659_);
v___x_3696_ = lean_array_push(v___x_3695_, v___x_3661_);
v___x_3697_ = lean_array_push(v___x_3696_, v___x_3662_);
v___x_3698_ = lean_array_push(v___x_3697_, v_a_3651_);
v___x_3699_ = lean_array_push(v___x_3698_, v___x_3691_);
v___x_3700_ = l_Lean_Meta_mkAppOptM(v___x_3655_, v___x_3699_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3719_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3719_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3719_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Meta_expandCoe(v_a_3701_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3717_; 
lean_del_object(v___x_3653_);
lean_dec(v_a_3437_);
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3717_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3717_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_fst_3710_; lean_object* v___x_3712_; 
v_fst_3710_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_fst_3710_);
lean_dec(v_a_3706_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set_tag(v___x_3703_, 1);
lean_ctor_set(v___x_3703_, 0, v_fst_3710_);
v___x_3712_ = v___x_3703_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_fst_3710_);
v___x_3712_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3714_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3712_);
v___x_3714_ = v___x_3708_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3718_; 
lean_del_object(v___x_3703_);
v_a_3718_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3705_);
v_a_3687_ = v_a_3718_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_3720_; 
v_a_3720_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3700_);
v_a_3687_ = v_a_3720_;
goto v___jp_3686_;
}
}
}
}
}
}
else
{
lean_object* v___x_3725_; 
lean_del_object(v___x_3653_);
lean_dec(v_a_3651_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3399_);
lean_dec_ref(v_e_3368_);
v___x_3725_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3437_, v_a_3371_, v_a_3373_);
lean_dec(v_a_3437_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___x_3725_, 0);
lean_dec(v_unused_3734_);
v___x_3727_ = v___x_3725_;
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v___x_3725_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(0);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3729_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3725_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3725_);
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
}
else
{
lean_dec(v_a_3437_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_dec(v_snd_3418_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_del_object(v___x_3399_);
lean_dec_ref(v_e_3368_);
return v___x_3650_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_a_3437_);
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3745_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3438_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3438_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3434_);
lean_dec(v_snd_3432_);
lean_dec(v_fst_3431_);
lean_del_object(v___x_3429_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3753_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3436_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3436_);
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
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_dec(v_a_3423_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3763_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3763_);
v___x_3765_ = v___x_3425_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3768_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3422_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3422_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_dec(v_a_3409_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v___x_3778_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3778_);
v___x_3780_ = v___x_3411_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3406_);
lean_dec(v_a_3404_);
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3783_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3408_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3408_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_del_object(v___x_3399_);
lean_dec(v_a_3397_);
lean_dec_ref(v_e_3368_);
v_a_3792_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3401_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3401_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3801_, lean_object* v_expectedType_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3801_, v_expectedType_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3809_, lean_object* v_expectedType_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v___x_3816_; 
lean_inc_ref(v_expectedType_3810_);
lean_inc_ref(v_expr_3809_);
v___x_3816_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3809_, v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3896_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3896_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3896_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
if (lean_obj_tag(v_a_3817_) == 1)
{
lean_object* v_val_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_val_3821_ = lean_ctor_get(v_a_3817_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3817_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3823_ = v_a_3817_;
v_isShared_3824_ = v_isSharedCheck_3833_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_val_3821_);
lean_dec(v_a_3817_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3833_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_val_3821_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3826_);
v___x_3828_ = v___x_3823_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3828_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v___x_3834_; 
lean_del_object(v___x_3819_);
lean_dec(v_a_3817_);
lean_inc_ref(v_expectedType_3810_);
v___x_3834_ = l_Lean_Meta_whnfR(v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; uint8_t v___x_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3834_);
v___x_3836_ = l_Lean_Expr_isForall(v_a_3835_);
lean_dec(v_a_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3809_, v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
return v___x_3837_;
}
else
{
lean_object* v___x_3838_; 
lean_inc_ref(v_expr_3809_);
v___x_3838_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3809_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
if (lean_obj_tag(v_a_3839_) == 1)
{
lean_object* v_val_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3878_; 
v_val_3840_ = lean_ctor_get(v_a_3839_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3839_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3842_ = v_a_3839_;
v_isShared_3843_ = v_isSharedCheck_3878_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_val_3840_);
lean_dec(v_a_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3878_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; 
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
lean_inc_ref(v_a_3811_);
lean_inc(v_val_3840_);
v___x_3844_ = lean_infer_type(v_val_3840_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
lean_inc_ref(v_expectedType_3810_);
v___x_3846_ = l_Lean_Meta_isExprDefEq(v_a_3845_, v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3861_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3861_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3861_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
uint8_t v___x_3851_; 
v___x_3851_ = lean_unbox(v_a_3847_);
lean_dec(v_a_3847_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
lean_del_object(v___x_3849_);
lean_del_object(v___x_3842_);
lean_dec(v_val_3840_);
v___x_3852_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3809_, v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
return v___x_3852_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v___x_3853_ = lean_box(0);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v_val_3840_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3854_);
v___x_3856_ = v___x_3842_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3858_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3856_);
v___x_3858_ = v___x_3849_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_del_object(v___x_3842_);
lean_dec(v_val_3840_);
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_a_3862_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3846_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3846_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_del_object(v___x_3842_);
lean_dec(v_val_3840_);
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_a_3870_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3844_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3844_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
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
}
else
{
lean_object* v___x_3879_; 
lean_dec(v_a_3839_);
v___x_3879_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3809_, v_expectedType_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
return v___x_3879_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_a_3880_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3838_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3838_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_a_3888_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3834_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3834_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec_ref(v_expectedType_3810_);
lean_dec_ref(v_expr_3809_);
v_a_3897_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3816_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3816_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3905_, lean_object* v_expectedType_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3905_, v_expectedType_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3913_, lean_object* v_expectedType_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3913_, v_expectedType_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3945_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3945_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3945_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
switch(lean_obj_tag(v_a_3921_))
{
case 0:
{
lean_object* v___x_3925_; lean_object* v___x_3927_; 
v___x_3925_ = lean_box(0);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3925_);
v___x_3927_ = v___x_3923_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
case 1:
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3940_; 
v_a_3929_ = lean_ctor_get(v_a_3921_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_a_3921_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3931_ = v_a_3921_;
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v_a_3921_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v_fst_3933_; lean_object* v___x_3935_; 
v_fst_3933_ = lean_ctor_get(v_a_3929_, 0);
lean_inc(v_fst_3933_);
lean_dec(v_a_3929_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v_fst_3933_);
v___x_3935_ = v___x_3931_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_fst_3933_);
v___x_3935_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3935_);
v___x_3937_ = v___x_3923_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
default: 
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_box(2);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3941_);
v___x_3943_ = v___x_3923_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
v_a_3946_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3920_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3920_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3954_, lean_object* v_expectedType_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Meta_coerce_x3f(v_expr_3954_, v_expectedType_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
return v_res_3961_;
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
