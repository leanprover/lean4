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
size_t v_x_37143__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_37143__boxed_301_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_res_302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_298_, v_x_37143__boxed_301_, v_x_300_);
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_481_; uint64_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1723u);
v___x_482_ = lean_uint64_of_nat(v___x_481_);
return v___x_482_;
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
v___x_502_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
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
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_nbuckets_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_939_ = lean_array_get_size(v_data_938_);
v___x_940_ = lean_unsigned_to_nat(2u);
v_nbuckets_941_ = lean_nat_mul(v___x_939_, v___x_940_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_box(0);
v___x_944_ = lean_mk_array(v_nbuckets_941_, v___x_943_);
v___x_945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_942_, v_data_938_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_946_, lean_object* v_a_947_, lean_object* v_b_948_){
_start:
{
lean_object* v_size_949_; lean_object* v_buckets_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_993_; 
v_size_949_ = lean_ctor_get(v_m_946_, 0);
v_buckets_950_ = lean_ctor_get(v_m_946_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_m_946_);
if (v_isSharedCheck_993_ == 0)
{
v___x_952_ = v_m_946_;
v_isShared_953_ = v_isSharedCheck_993_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_buckets_950_);
lean_inc(v_size_949_);
lean_dec(v_m_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_993_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v___x_957_; uint64_t v_fold_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v_bkt_967_; uint8_t v___x_968_; 
v___x_954_ = lean_array_get_size(v_buckets_950_);
v___x_955_ = l_Lean_ExprStructEq_hash(v_a_947_);
v___x_956_ = 32ULL;
v___x_957_ = lean_uint64_shift_right(v___x_955_, v___x_956_);
v_fold_958_ = lean_uint64_xor(v___x_955_, v___x_957_);
v___x_959_ = 16ULL;
v___x_960_ = lean_uint64_shift_right(v_fold_958_, v___x_959_);
v___x_961_ = lean_uint64_xor(v_fold_958_, v___x_960_);
v___x_962_ = lean_uint64_to_usize(v___x_961_);
v___x_963_ = lean_usize_of_nat(v___x_954_);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_sub(v___x_963_, v___x_964_);
v___x_966_ = lean_usize_land(v___x_962_, v___x_965_);
v_bkt_967_ = lean_array_uget_borrowed(v_buckets_950_, v___x_966_);
v___x_968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_947_, v_bkt_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v_size_x27_970_; lean_object* v___x_971_; lean_object* v_buckets_x27_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_969_ = lean_unsigned_to_nat(1u);
v_size_x27_970_ = lean_nat_add(v_size_949_, v___x_969_);
lean_dec(v_size_949_);
lean_inc(v_bkt_967_);
v___x_971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_971_, 0, v_a_947_);
lean_ctor_set(v___x_971_, 1, v_b_948_);
lean_ctor_set(v___x_971_, 2, v_bkt_967_);
v_buckets_x27_972_ = lean_array_uset(v_buckets_950_, v___x_966_, v___x_971_);
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = lean_nat_mul(v_size_x27_970_, v___x_973_);
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = lean_nat_div(v___x_974_, v___x_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_array_get_size(v_buckets_x27_972_);
v___x_978_ = lean_nat_dec_le(v___x_976_, v___x_977_);
lean_dec(v___x_976_);
if (v___x_978_ == 0)
{
lean_object* v_val_979_; lean_object* v___x_981_; 
v_val_979_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_972_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_val_979_);
lean_ctor_set(v___x_952_, 0, v_size_x27_970_);
v___x_981_ = v___x_952_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_size_x27_970_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_val_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_984_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_buckets_x27_972_);
lean_ctor_set(v___x_952_, 0, v_size_x27_970_);
v___x_984_ = v___x_952_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_size_x27_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_buckets_x27_972_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v___x_986_; lean_object* v_buckets_x27_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
lean_inc(v_bkt_967_);
v___x_986_ = lean_box(0);
v_buckets_x27_987_ = lean_array_uset(v_buckets_950_, v___x_966_, v___x_986_);
v___x_988_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_947_, v_b_948_, v_bkt_967_);
v___x_989_ = lean_array_uset(v_buckets_x27_987_, v___x_966_, v___x_988_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_989_);
v___x_991_ = v___x_952_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_size_949_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_994_, lean_object* v_e_995_, lean_object* v_fst_996_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = lean_st_ref_take(v_a_994_);
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_998_, v_e_995_, v_fst_996_);
v___x_1000_ = lean_st_ref_set(v_a_994_, v___x_999_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1002_, lean_object* v_e_1003_, lean_object* v_fst_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1002_, v_e_1003_, v_fst_1004_);
lean_dec(v_a_1002_);
return v_res_1006_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = l_Lean_maxRecDepthErrorMessage;
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1015_ = l_Lean_MessageData_ofFormat(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1017_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1018_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_ref_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___y_1036_; lean_object* v_fileName_1053_; lean_object* v_fileMap_1054_; lean_object* v_options_1055_; lean_object* v_currRecDepth_1056_; lean_object* v_maxRecDepth_1057_; lean_object* v_ref_1058_; lean_object* v_currNamespace_1059_; lean_object* v_openDecls_1060_; lean_object* v_initHeartbeats_1061_; lean_object* v_maxHeartbeats_1062_; lean_object* v_quotContext_1063_; lean_object* v_currMacroScope_1064_; uint8_t v_diag_1065_; lean_object* v_cancelTk_x3f_1066_; uint8_t v_suppressElabErrors_1067_; lean_object* v_inheritedTraceOptions_1068_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_fileName_1053_ = lean_ctor_get(v___y_1032_, 0);
v_fileMap_1054_ = lean_ctor_get(v___y_1032_, 1);
v_options_1055_ = lean_ctor_get(v___y_1032_, 2);
v_currRecDepth_1056_ = lean_ctor_get(v___y_1032_, 3);
v_maxRecDepth_1057_ = lean_ctor_get(v___y_1032_, 4);
v_ref_1058_ = lean_ctor_get(v___y_1032_, 5);
v_currNamespace_1059_ = lean_ctor_get(v___y_1032_, 6);
v_openDecls_1060_ = lean_ctor_get(v___y_1032_, 7);
v_initHeartbeats_1061_ = lean_ctor_get(v___y_1032_, 8);
v_maxHeartbeats_1062_ = lean_ctor_get(v___y_1032_, 9);
v_quotContext_1063_ = lean_ctor_get(v___y_1032_, 10);
v_currMacroScope_1064_ = lean_ctor_get(v___y_1032_, 11);
v_diag_1065_ = lean_ctor_get_uint8(v___y_1032_, sizeof(void*)*14);
v_cancelTk_x3f_1066_ = lean_ctor_get(v___y_1032_, 12);
v_suppressElabErrors_1067_ = lean_ctor_get_uint8(v___y_1032_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1068_ = lean_ctor_get(v___y_1032_, 13);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_dec_eq(v_maxRecDepth_1057_, v___x_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_nat_dec_eq(v_currRecDepth_1056_, v_maxRecDepth_1057_);
if (v___x_1076_ == 0)
{
goto v___jp_1069_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v___y_1029_);
lean_dec_ref(v_x_1027_);
lean_inc(v_ref_1058_);
v___x_1077_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1058_);
v___y_1036_ = v___x_1077_;
goto v___jp_1035_;
}
}
else
{
goto v___jp_1069_;
}
v___jp_1035_:
{
if (lean_obj_tag(v___y_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___y_1036_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___y_1036_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___y_1036_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___y_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___y_1036_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___y_1036_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___y_1036_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___y_1036_);
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
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v_currRecDepth_1056_, v___x_1070_);
lean_inc_ref(v_inheritedTraceOptions_1068_);
lean_inc(v_cancelTk_x3f_1066_);
lean_inc(v_currMacroScope_1064_);
lean_inc(v_quotContext_1063_);
lean_inc(v_maxHeartbeats_1062_);
lean_inc(v_initHeartbeats_1061_);
lean_inc(v_openDecls_1060_);
lean_inc(v_currNamespace_1059_);
lean_inc(v_ref_1058_);
lean_inc(v_maxRecDepth_1057_);
lean_inc_ref(v_options_1055_);
lean_inc_ref(v_fileMap_1054_);
lean_inc_ref(v_fileName_1053_);
v___x_1072_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1072_, 0, v_fileName_1053_);
lean_ctor_set(v___x_1072_, 1, v_fileMap_1054_);
lean_ctor_set(v___x_1072_, 2, v_options_1055_);
lean_ctor_set(v___x_1072_, 3, v___x_1071_);
lean_ctor_set(v___x_1072_, 4, v_maxRecDepth_1057_);
lean_ctor_set(v___x_1072_, 5, v_ref_1058_);
lean_ctor_set(v___x_1072_, 6, v_currNamespace_1059_);
lean_ctor_set(v___x_1072_, 7, v_openDecls_1060_);
lean_ctor_set(v___x_1072_, 8, v_initHeartbeats_1061_);
lean_ctor_set(v___x_1072_, 9, v_maxHeartbeats_1062_);
lean_ctor_set(v___x_1072_, 10, v_quotContext_1063_);
lean_ctor_set(v___x_1072_, 11, v_currMacroScope_1064_);
lean_ctor_set(v___x_1072_, 12, v_cancelTk_x3f_1066_);
lean_ctor_set(v___x_1072_, 13, v_inheritedTraceOptions_1068_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*14, v_diag_1065_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*14 + 1, v_suppressElabErrors_1067_);
lean_inc(v___y_1033_);
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
lean_inc(v___y_1028_);
v___x_1073_ = lean_apply_7(v_x_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___x_1072_, v___y_1033_, lean_box(0));
v___y_1036_ = v___x_1073_;
goto v___jp_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
else
{
lean_object* v_key_1090_; lean_object* v_value_1091_; lean_object* v_tail_1092_; uint8_t v___x_1093_; 
v_key_1090_ = lean_ctor_get(v_x_1088_, 0);
v_value_1091_ = lean_ctor_get(v_x_1088_, 1);
v_tail_1092_ = lean_ctor_get(v_x_1088_, 2);
v___x_1093_ = l_Lean_ExprStructEq_beq(v_key_1090_, v_a_1087_);
if (v___x_1093_ == 0)
{
v_x_1088_ = v_tail_1092_;
goto _start;
}
else
{
lean_object* v___x_1095_; 
lean_inc(v_value_1091_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_value_1091_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(lean_object* v_a_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1096_, v_x_1097_);
lean_dec(v_x_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_buckets_1101_; lean_object* v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v_fold_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_buckets_1101_ = lean_ctor_get(v_m_1099_, 1);
v___x_1102_ = lean_array_get_size(v_buckets_1101_);
v___x_1103_ = l_Lean_ExprStructEq_hash(v_a_1100_);
v___x_1104_ = 32ULL;
v___x_1105_ = lean_uint64_shift_right(v___x_1103_, v___x_1104_);
v_fold_1106_ = lean_uint64_xor(v___x_1103_, v___x_1105_);
v___x_1107_ = 16ULL;
v___x_1108_ = lean_uint64_shift_right(v_fold_1106_, v___x_1107_);
v___x_1109_ = lean_uint64_xor(v_fold_1106_, v___x_1108_);
v___x_1110_ = lean_uint64_to_usize(v___x_1109_);
v___x_1111_ = lean_usize_of_nat(v___x_1102_);
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_sub(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_usize_land(v___x_1110_, v___x_1113_);
v___x_1115_ = lean_array_uget_borrowed(v_buckets_1101_, v___x_1114_);
v___x_1116_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_1100_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_1117_, v_a_1118_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_m_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_apply_1(v_x_1121_, lean_box(0));
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___y_1122_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1131_, v_x_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1143_, lean_object* v_pre_1144_, lean_object* v_post_1145_, uint8_t v_usedLetOnly_1146_, uint8_t v_skipConstInApp_1147_, uint8_t v_skipInstances_1148_, lean_object* v_body_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_array_push(v_fvars_1143_, v_x_1150_);
v___x_1159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1144_, v_post_1145_, v_usedLetOnly_1146_, v_skipConstInApp_1147_, v_skipInstances_1148_, v___x_1158_, v_body_1149_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1160_, lean_object* v_pre_1161_, lean_object* v_post_1162_, lean_object* v_usedLetOnly_1163_, lean_object* v_skipConstInApp_1164_, lean_object* v_skipInstances_1165_, lean_object* v_body_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_usedLetOnly_boxed_1175_; uint8_t v_skipConstInApp_boxed_1176_; uint8_t v_skipInstances_boxed_1177_; lean_object* v_res_1178_; 
v_usedLetOnly_boxed_1175_ = lean_unbox(v_usedLetOnly_1163_);
v_skipConstInApp_boxed_1176_ = lean_unbox(v_skipConstInApp_1164_);
v_skipInstances_boxed_1177_ = lean_unbox(v_skipInstances_1165_);
v_res_1178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1160_, v_pre_1161_, v_post_1162_, v_usedLetOnly_boxed_1175_, v_skipConstInApp_boxed_1176_, v_skipInstances_boxed_1177_, v_body_1166_, v_x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1168_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1179_, lean_object* v_post_1180_, uint8_t v_usedLetOnly_1181_, uint8_t v_skipConstInApp_1182_, uint8_t v_skipInstances_1183_, lean_object* v_e_1184_, lean_object* v_a_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
lean_inc_ref(v_post_1180_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc_ref(v_e_1184_);
v___x_1192_ = lean_apply_7(v_post_1180_, v_e_1184_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1224_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1223_; 
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1200_ = v_a_1193_;
v_isShared_1201_ = v_isSharedCheck_1223_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_inc(v_fst_1197_);
lean_dec(v_a_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1223_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___y_1203_; 
switch(lean_obj_tag(v_fst_1197_))
{
case 0:
{
lean_object* v_e_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
lean_del_object(v___x_1200_);
lean_del_object(v___x_1195_);
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_post_1180_);
lean_dec_ref(v_pre_1179_);
v_e_1210_ = lean_ctor_get(v_fst_1197_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_fst_1197_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v_fst_1197_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_e_1210_);
lean_dec(v_fst_1197_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_e_1210_);
lean_ctor_set(v___x_1214_, 1, v_snd_1198_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
case 1:
{
lean_object* v_e_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1200_);
lean_del_object(v___x_1195_);
lean_dec_ref(v_e_1184_);
v_e_1219_ = lean_ctor_get(v_fst_1197_, 0);
lean_inc_ref(v_e_1219_);
lean_dec_ref_known(v_fst_1197_, 1);
v___x_1220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1179_, v_post_1180_, v_usedLetOnly_1181_, v_skipConstInApp_1182_, v_skipInstances_1183_, v_e_1219_, v_a_1185_, v_snd_1198_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1220_;
}
default: 
{
lean_object* v_e_x3f_1221_; 
lean_dec_ref(v_post_1180_);
lean_dec_ref(v_pre_1179_);
v_e_x3f_1221_ = lean_ctor_get(v_fst_1197_, 0);
lean_inc(v_e_x3f_1221_);
lean_dec_ref_known(v_fst_1197_, 1);
if (lean_obj_tag(v_e_x3f_1221_) == 0)
{
v___y_1203_ = v_e_1184_;
goto v___jp_1202_;
}
else
{
lean_object* v_val_1222_; 
lean_dec_ref(v_e_1184_);
v_val_1222_ = lean_ctor_get(v_e_x3f_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v_e_x3f_1221_, 1);
v___y_1203_ = v_val_1222_;
goto v___jp_1202_;
}
}
}
v___jp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___y_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___y_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_snd_1198_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1205_);
v___x_1207_ = v___x_1195_;
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
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_e_1184_);
lean_dec_ref(v_post_1180_);
lean_dec_ref(v_pre_1179_);
v_a_1225_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1192_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1192_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1233_, lean_object* v_post_1234_, uint8_t v_usedLetOnly_1235_, uint8_t v_skipConstInApp_1236_, uint8_t v_skipInstances_1237_, lean_object* v_fvars_1238_, lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
if (lean_obj_tag(v_e_1239_) == 6)
{
lean_object* v_binderName_1247_; lean_object* v_binderType_1248_; lean_object* v_body_1249_; uint8_t v_binderInfo_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_binderName_1247_ = lean_ctor_get(v_e_1239_, 0);
lean_inc(v_binderName_1247_);
v_binderType_1248_ = lean_ctor_get(v_e_1239_, 1);
lean_inc_ref(v_binderType_1248_);
v_body_1249_ = lean_ctor_get(v_e_1239_, 2);
lean_inc_ref(v_body_1249_);
v_binderInfo_1250_ = lean_ctor_get_uint8(v_e_1239_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1251_ = lean_expr_instantiate_rev(v_binderType_1248_, v_fvars_1238_);
lean_dec_ref(v_binderType_1248_);
lean_inc_ref(v_post_1234_);
lean_inc_ref(v_pre_1233_);
v___x_1252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1233_, v_post_1234_, v_usedLetOnly_1235_, v_skipConstInApp_1236_, v_skipInstances_1237_, v___x_1251_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_fst_1254_ = lean_ctor_get(v_a_1253_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_a_1253_, 1);
lean_inc(v_snd_1255_);
lean_dec(v_a_1253_);
v___x_1256_ = lean_box(v_usedLetOnly_1235_);
v___x_1257_ = lean_box(v_skipConstInApp_1236_);
v___x_1258_ = lean_box(v_skipInstances_1237_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1259_, 0, v_fvars_1238_);
lean_closure_set(v___f_1259_, 1, v_pre_1233_);
lean_closure_set(v___f_1259_, 2, v_post_1234_);
lean_closure_set(v___f_1259_, 3, v___x_1256_);
lean_closure_set(v___f_1259_, 4, v___x_1257_);
lean_closure_set(v___f_1259_, 5, v___x_1258_);
lean_closure_set(v___f_1259_, 6, v_body_1249_);
v___x_1260_ = 0;
v___x_1261_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1247_, v_binderInfo_1250_, v_fst_1254_, v___f_1259_, v___x_1260_, v_a_1240_, v_snd_1255_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1261_;
}
else
{
lean_dec_ref(v_body_1249_);
lean_dec(v_binderName_1247_);
lean_dec_ref(v_fvars_1238_);
lean_dec_ref(v_post_1234_);
lean_dec_ref(v_pre_1233_);
return v___x_1252_;
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_expr_instantiate_rev(v_e_1239_, v_fvars_1238_);
lean_dec_ref(v_e_1239_);
lean_inc_ref(v_post_1234_);
lean_inc_ref(v_pre_1233_);
v___x_1263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1233_, v_post_1234_, v_usedLetOnly_1235_, v_skipConstInApp_1236_, v_skipInstances_1237_, v___x_1262_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; uint8_t v___x_1267_; uint8_t v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v_fst_1265_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_fst_1265_);
v_snd_1266_ = lean_ctor_get(v_a_1264_, 1);
lean_inc(v_snd_1266_);
lean_dec(v_a_1264_);
v___x_1267_ = 0;
v___x_1268_ = 1;
v___x_1269_ = 1;
v___x_1270_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1238_, v_fst_1265_, v___x_1267_, v_usedLetOnly_1235_, v___x_1267_, v___x_1268_, v___x_1269_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec_ref(v_fvars_1238_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1233_, v_post_1234_, v_usedLetOnly_1235_, v_skipConstInApp_1236_, v_skipInstances_1237_, v_a_1271_, v_a_1240_, v_snd_1266_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_snd_1266_);
lean_dec_ref(v_post_1234_);
lean_dec_ref(v_pre_1233_);
v_a_1273_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1270_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1238_);
lean_dec_ref(v_post_1234_);
lean_dec_ref(v_pre_1233_);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1281_, lean_object* v_pre_1282_, lean_object* v_post_1283_, uint8_t v_usedLetOnly_1284_, uint8_t v_skipConstInApp_1285_, uint8_t v_skipInstances_1286_, lean_object* v_body_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_array_push(v_fvars_1281_, v_x_1288_);
v___x_1297_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1282_, v_post_1283_, v_usedLetOnly_1284_, v_skipConstInApp_1285_, v_skipInstances_1286_, v___x_1296_, v_body_1287_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1298_, lean_object* v_pre_1299_, lean_object* v_post_1300_, lean_object* v_usedLetOnly_1301_, lean_object* v_skipConstInApp_1302_, lean_object* v_skipInstances_1303_, lean_object* v_body_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_usedLetOnly_boxed_1313_; uint8_t v_skipConstInApp_boxed_1314_; uint8_t v_skipInstances_boxed_1315_; lean_object* v_res_1316_; 
v_usedLetOnly_boxed_1313_ = lean_unbox(v_usedLetOnly_1301_);
v_skipConstInApp_boxed_1314_ = lean_unbox(v_skipConstInApp_1302_);
v_skipInstances_boxed_1315_ = lean_unbox(v_skipInstances_1303_);
v_res_1316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1298_, v_pre_1299_, v_post_1300_, v_usedLetOnly_boxed_1313_, v_skipConstInApp_boxed_1314_, v_skipInstances_boxed_1315_, v_body_1304_, v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1306_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1317_, lean_object* v_post_1318_, uint8_t v_usedLetOnly_1319_, uint8_t v_skipConstInApp_1320_, uint8_t v_skipInstances_1321_, lean_object* v_fvars_1322_, lean_object* v_e_1323_, lean_object* v_a_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
if (lean_obj_tag(v_e_1323_) == 8)
{
lean_object* v_declName_1331_; lean_object* v_type_1332_; lean_object* v_value_1333_; lean_object* v_body_1334_; uint8_t v_nondep_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_declName_1331_ = lean_ctor_get(v_e_1323_, 0);
lean_inc(v_declName_1331_);
v_type_1332_ = lean_ctor_get(v_e_1323_, 1);
lean_inc_ref(v_type_1332_);
v_value_1333_ = lean_ctor_get(v_e_1323_, 2);
lean_inc_ref(v_value_1333_);
v_body_1334_ = lean_ctor_get(v_e_1323_, 3);
lean_inc_ref(v_body_1334_);
v_nondep_1335_ = lean_ctor_get_uint8(v_e_1323_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1323_, 4);
v___x_1336_ = lean_expr_instantiate_rev(v_type_1332_, v_fvars_1322_);
lean_dec_ref(v_type_1332_);
lean_inc_ref(v_post_1318_);
lean_inc_ref(v_pre_1317_);
v___x_1337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1317_, v_post_1318_, v_usedLetOnly_1319_, v_skipConstInApp_1320_, v_skipInstances_1321_, v___x_1336_, v_a_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v_fst_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_fst_1339_);
v_snd_1340_ = lean_ctor_get(v_a_1338_, 1);
lean_inc(v_snd_1340_);
lean_dec(v_a_1338_);
v___x_1341_ = lean_expr_instantiate_rev(v_value_1333_, v_fvars_1322_);
lean_dec_ref(v_value_1333_);
lean_inc_ref(v_post_1318_);
lean_inc_ref(v_pre_1317_);
v___x_1342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1317_, v_post_1318_, v_usedLetOnly_1319_, v_skipConstInApp_1320_, v_skipInstances_1321_, v___x_1341_, v_a_1324_, v_snd_1340_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_fst_1344_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_fst_1344_);
v_snd_1345_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_snd_1345_);
lean_dec(v_a_1343_);
v___x_1346_ = lean_box(v_usedLetOnly_1319_);
v___x_1347_ = lean_box(v_skipConstInApp_1320_);
v___x_1348_ = lean_box(v_skipInstances_1321_);
v___f_1349_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1349_, 0, v_fvars_1322_);
lean_closure_set(v___f_1349_, 1, v_pre_1317_);
lean_closure_set(v___f_1349_, 2, v_post_1318_);
lean_closure_set(v___f_1349_, 3, v___x_1346_);
lean_closure_set(v___f_1349_, 4, v___x_1347_);
lean_closure_set(v___f_1349_, 5, v___x_1348_);
lean_closure_set(v___f_1349_, 6, v_body_1334_);
v___x_1350_ = 0;
v___x_1351_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1331_, v_fst_1339_, v_fst_1344_, v___f_1349_, v_nondep_1335_, v___x_1350_, v_a_1324_, v_snd_1345_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1351_;
}
else
{
lean_dec(v_fst_1339_);
lean_dec_ref(v_body_1334_);
lean_dec(v_declName_1331_);
lean_dec_ref(v_fvars_1322_);
lean_dec_ref(v_post_1318_);
lean_dec_ref(v_pre_1317_);
return v___x_1342_;
}
}
else
{
lean_dec_ref(v_body_1334_);
lean_dec_ref(v_value_1333_);
lean_dec(v_declName_1331_);
lean_dec_ref(v_fvars_1322_);
lean_dec_ref(v_post_1318_);
lean_dec_ref(v_pre_1317_);
return v___x_1337_;
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_expr_instantiate_rev(v_e_1323_, v_fvars_1322_);
lean_dec_ref(v_e_1323_);
lean_inc_ref(v_post_1318_);
lean_inc_ref(v_pre_1317_);
v___x_1353_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1317_, v_post_1318_, v_usedLetOnly_1319_, v_skipConstInApp_1320_, v_skipInstances_1321_, v___x_1352_, v_a_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_fst_1355_; lean_object* v_snd_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v_fst_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_fst_1355_);
v_snd_1356_ = lean_ctor_get(v_a_1354_, 1);
lean_inc(v_snd_1356_);
lean_dec(v_a_1354_);
v___x_1357_ = 0;
v___x_1358_ = 1;
v___x_1359_ = l_Lean_Meta_mkLetFVars(v_fvars_1322_, v_fst_1355_, v_usedLetOnly_1319_, v___x_1357_, v___x_1358_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v_fvars_1322_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1317_, v_post_1318_, v_usedLetOnly_1319_, v_skipConstInApp_1320_, v_skipInstances_1321_, v_a_1360_, v_a_1324_, v_snd_1356_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_snd_1356_);
lean_dec_ref(v_post_1318_);
lean_dec_ref(v_pre_1317_);
v_a_1362_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1359_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1322_);
lean_dec_ref(v_post_1318_);
lean_dec_ref(v_pre_1317_);
return v___x_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(lean_object* v_pre_1370_, lean_object* v_post_1371_, uint8_t v_usedLetOnly_1372_, uint8_t v_skipConstInApp_1373_, uint8_t v_skipInstances_1374_, size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_bs_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_lt(v_i_1376_, v_sz_1375_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref(v_post_1371_);
lean_dec_ref(v_pre_1370_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_bs_1377_);
lean_ctor_set(v___x_1386_, 1, v___y_1379_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_v_1388_; lean_object* v___x_1389_; 
v_v_1388_ = lean_array_uget_borrowed(v_bs_1377_, v_i_1376_);
lean_inc(v_v_1388_);
lean_inc_ref(v_post_1371_);
lean_inc_ref(v_pre_1370_);
v___x_1389_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1370_, v_post_1371_, v_usedLetOnly_1372_, v_skipConstInApp_1373_, v_skipInstances_1374_, v_v_1388_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; lean_object* v_bs_x27_1394_; size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_fst_1391_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v_a_1390_, 1);
lean_inc(v_snd_1392_);
lean_dec(v_a_1390_);
v___x_1393_ = lean_unsigned_to_nat(0u);
v_bs_x27_1394_ = lean_array_uset(v_bs_1377_, v_i_1376_, v___x_1393_);
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1376_, v___x_1395_);
v___x_1397_ = lean_array_uset(v_bs_x27_1394_, v_i_1376_, v_fst_1391_);
v_i_1376_ = v___x_1396_;
v_bs_1377_ = v___x_1397_;
v___y_1379_ = v_snd_1392_;
goto _start;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_bs_1377_);
lean_dec_ref(v_post_1371_);
lean_dec_ref(v_pre_1370_);
v_a_1399_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1389_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1389_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(lean_object* v_pre_1407_, lean_object* v_post_1408_, uint8_t v_usedLetOnly_1409_, uint8_t v_skipConstInApp_1410_, uint8_t v_skipInstances_1411_, lean_object* v___x_1412_, lean_object* v___y_1413_, lean_object* v_b_1414_, lean_object* v_a_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1407_, v_post_1408_, v_usedLetOnly_1409_, v_skipConstInApp_1410_, v_skipInstances_1411_, v___x_1412_, v___y_1413_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1441_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1441_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1441_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1440_; 
v_fst_1427_ = lean_ctor_get(v_a_1423_, 0);
v_snd_1428_ = lean_ctor_get(v_a_1423_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1423_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1430_ = v_a_1423_;
v_isShared_1431_ = v_isSharedCheck_1440_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snd_1428_);
lean_inc(v_fst_1427_);
lean_dec(v_a_1423_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1440_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = lean_array_fset(v_b_1414_, v_a_1415_, v_fst_1427_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1433_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_snd_1428_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1435_);
v___x_1437_ = v___x_1425_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v_b_1414_);
v_a_1442_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1422_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1422_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v_pre_1450_, lean_object* v_post_1451_, lean_object* v_usedLetOnly_1452_, lean_object* v_skipConstInApp_1453_, lean_object* v_skipInstances_1454_, lean_object* v___x_1455_, lean_object* v___y_1456_, lean_object* v_b_1457_, lean_object* v_a_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v_usedLetOnly_boxed_1465_; uint8_t v_skipConstInApp_boxed_1466_; uint8_t v_skipInstances_boxed_1467_; lean_object* v_res_1468_; 
v_usedLetOnly_boxed_1465_ = lean_unbox(v_usedLetOnly_1452_);
v_skipConstInApp_boxed_1466_ = lean_unbox(v_skipConstInApp_1453_);
v_skipInstances_boxed_1467_ = lean_unbox(v_skipInstances_1454_);
v_res_1468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_1450_, v_post_1451_, v_usedLetOnly_boxed_1465_, v_skipConstInApp_boxed_1466_, v_skipInstances_boxed_1467_, v___x_1455_, v___y_1456_, v_b_1457_, v_a_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1458_);
lean_dec(v___y_1456_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(lean_object* v_upperBound_1469_, lean_object* v___x_1470_, lean_object* v_pre_1471_, lean_object* v_post_1472_, uint8_t v_usedLetOnly_1473_, uint8_t v_skipConstInApp_1474_, uint8_t v_skipInstances_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___y_1486_; uint8_t v___x_1520_; 
v___x_1520_ = lean_nat_dec_lt(v_a_1476_, v_upperBound_1469_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_a_1476_);
lean_dec_ref(v_post_1472_);
lean_dec_ref(v_pre_1471_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_b_1477_);
lean_ctor_set(v___x_1521_, 1, v___y_1479_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_fget_borrowed(v_b_1477_, v_a_1476_);
v___x_1524_ = lean_array_get_size(v___x_1470_);
v___x_1525_ = lean_nat_dec_lt(v_a_1476_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; 
lean_inc(v___x_1523_);
v___x_1526_ = lean_box(v_usedLetOnly_1473_);
v___x_1527_ = lean_box(v_skipConstInApp_1474_);
v___x_1528_ = lean_box(v_skipInstances_1475_);
lean_inc(v_a_1476_);
lean_inc(v___y_1478_);
lean_inc_ref(v_post_1472_);
lean_inc_ref(v_pre_1471_);
v___f_1529_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1529_, 0, v_pre_1471_);
lean_closure_set(v___f_1529_, 1, v_post_1472_);
lean_closure_set(v___f_1529_, 2, v___x_1526_);
lean_closure_set(v___f_1529_, 3, v___x_1527_);
lean_closure_set(v___f_1529_, 4, v___x_1528_);
lean_closure_set(v___f_1529_, 5, v___x_1523_);
lean_closure_set(v___f_1529_, 6, v___y_1478_);
lean_closure_set(v___f_1529_, 7, v_b_1477_);
lean_closure_set(v___f_1529_, 8, v_a_1476_);
v___y_1486_ = v___f_1529_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1530_; uint8_t v_isInstance_1531_; 
v___x_1530_ = lean_array_fget_borrowed(v___x_1470_, v_a_1476_);
v_isInstance_1531_ = lean_ctor_get_uint8(v___x_1530_, sizeof(void*)*1 + 4);
if (v_isInstance_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; 
lean_inc(v___x_1523_);
v___x_1532_ = lean_box(v_usedLetOnly_1473_);
v___x_1533_ = lean_box(v_skipConstInApp_1474_);
v___x_1534_ = lean_box(v_skipInstances_1475_);
lean_inc(v_a_1476_);
lean_inc(v___y_1478_);
lean_inc_ref(v_post_1472_);
lean_inc_ref(v_pre_1471_);
v___f_1535_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1535_, 0, v_pre_1471_);
lean_closure_set(v___f_1535_, 1, v_post_1472_);
lean_closure_set(v___f_1535_, 2, v___x_1532_);
lean_closure_set(v___f_1535_, 3, v___x_1533_);
lean_closure_set(v___f_1535_, 4, v___x_1534_);
lean_closure_set(v___f_1535_, 5, v___x_1523_);
lean_closure_set(v___f_1535_, 6, v___y_1478_);
lean_closure_set(v___f_1535_, 7, v_b_1477_);
lean_closure_set(v___f_1535_, 8, v_a_1476_);
v___y_1486_ = v___f_1535_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1536_; lean_object* v___f_1537_; 
v___x_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_b_1477_);
v___f_1537_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1537_, 0, v___x_1536_);
v___y_1486_ = v___f_1537_;
goto v___jp_1485_;
}
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; 
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
v___x_1487_ = lean_apply_6(v___y_1486_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1511_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1511_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1511_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_fst_1492_; 
v_fst_1492_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_fst_1492_);
if (lean_obj_tag(v_fst_1492_) == 0)
{
lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_a_1476_);
lean_dec_ref(v_post_1472_);
lean_dec_ref(v_pre_1471_);
v_snd_1493_ = lean_ctor_get(v_a_1488_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_a_1488_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_a_1488_, 0);
lean_dec(v_unused_1505_);
v___x_1495_ = v_a_1488_;
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_dec(v_a_1488_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_a_1497_; lean_object* v___x_1499_; 
v_a_1497_ = lean_ctor_get(v_fst_1492_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v_fst_1492_, 1);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_a_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1493_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1499_);
v___x_1501_ = v___x_1490_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_snd_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_del_object(v___x_1490_);
v_snd_1506_ = lean_ctor_get(v_a_1488_, 1);
lean_inc(v_snd_1506_);
lean_dec(v_a_1488_);
v_a_1507_ = lean_ctor_get(v_fst_1492_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v_fst_1492_, 1);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v_a_1476_, v___x_1508_);
lean_dec(v_a_1476_);
v_a_1476_ = v___x_1509_;
v_b_1477_ = v_a_1507_;
v___y_1479_ = v_snd_1506_;
goto _start;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_a_1476_);
lean_dec_ref(v_post_1472_);
lean_dec_ref(v_pre_1471_);
v_a_1512_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1487_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1487_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(uint8_t v_skipInstances_1538_, lean_object* v_pre_1539_, lean_object* v_post_1540_, uint8_t v_usedLetOnly_1541_, uint8_t v_skipConstInApp_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_f_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; 
if (lean_obj_tag(v_x_1543_) == 5)
{
lean_object* v_fn_1609_; lean_object* v_arg_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_fn_1609_ = lean_ctor_get(v_x_1543_, 0);
lean_inc_ref(v_fn_1609_);
v_arg_1610_ = lean_ctor_get(v_x_1543_, 1);
lean_inc_ref(v_arg_1610_);
lean_dec_ref_known(v_x_1543_, 2);
v___x_1611_ = lean_array_set(v_x_1544_, v_x_1545_, v_arg_1610_);
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = lean_nat_sub(v_x_1545_, v___x_1612_);
lean_dec(v_x_1545_);
v_x_1543_ = v_fn_1609_;
v_x_1544_ = v___x_1611_;
v_x_1545_ = v___x_1613_;
goto _start;
}
else
{
lean_dec(v_x_1545_);
if (v_skipConstInApp_1542_ == 0)
{
goto v___jp_1604_;
}
else
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Lean_Expr_isConst(v_x_1543_);
if (v___x_1615_ == 0)
{
goto v___jp_1604_;
}
else
{
v_f_1554_ = v_x_1543_;
v___y_1555_ = v___y_1546_;
v___y_1556_ = v___y_1547_;
v___y_1557_ = v___y_1548_;
v___y_1558_ = v___y_1549_;
v___y_1559_ = v___y_1550_;
v___y_1560_ = v___y_1551_;
goto v___jp_1553_;
}
}
}
v___jp_1553_:
{
if (v_skipInstances_1538_ == 0)
{
size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_sz_1561_ = lean_array_size(v_x_1544_);
v___x_1562_ = ((size_t)0ULL);
lean_inc_ref(v_post_1540_);
lean_inc_ref(v_pre_1539_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1538_, v_sz_1561_, v___x_1562_, v_x_1544_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v_fst_1565_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_a_1564_);
v___x_1567_ = l_Lean_mkAppN(v_f_1554_, v_fst_1565_);
lean_dec(v_fst_1565_);
v___x_1568_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1538_, v___x_1567_, v___y_1555_, v_snd_1566_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1568_;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_f_1554_);
lean_dec_ref(v_post_1540_);
lean_dec_ref(v_pre_1539_);
v_a_1569_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1563_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1563_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_array_get_size(v_x_1544_);
lean_inc_ref(v_f_1554_);
v___x_1578_ = l_Lean_Meta_getFunInfoNArgs(v_f_1554_, v___x_1577_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_paramInfo_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v_paramInfo_1580_ = lean_ctor_get(v_a_1579_, 0);
lean_inc_ref(v_paramInfo_1580_);
lean_dec(v_a_1579_);
v___x_1581_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1540_);
lean_inc_ref(v_pre_1539_);
v___x_1582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_1577_, v_paramInfo_1580_, v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1538_, v___x_1581_, v_x_1544_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec_ref(v_paramInfo_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_fst_1584_ = lean_ctor_get(v_a_1583_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_a_1583_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_a_1583_);
v___x_1586_ = l_Lean_mkAppN(v_f_1554_, v_fst_1584_);
lean_dec(v_fst_1584_);
v___x_1587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1538_, v___x_1586_, v___y_1555_, v_snd_1585_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1587_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_f_1554_);
lean_dec_ref(v_post_1540_);
lean_dec_ref(v_pre_1539_);
v_a_1588_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1582_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1582_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v___y_1556_);
lean_dec_ref(v_f_1554_);
lean_dec_ref(v_x_1544_);
lean_dec_ref(v_post_1540_);
lean_dec_ref(v_pre_1539_);
v_a_1596_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1578_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1578_);
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
}
v___jp_1604_:
{
lean_object* v___x_1605_; 
lean_inc_ref(v_post_1540_);
lean_inc_ref(v_pre_1539_);
v___x_1605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1538_, v_x_1543_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v_fst_1607_ = lean_ctor_get(v_a_1606_, 0);
lean_inc(v_fst_1607_);
v_snd_1608_ = lean_ctor_get(v_a_1606_, 1);
lean_inc(v_snd_1608_);
lean_dec(v_a_1606_);
v_f_1554_ = v_fst_1607_;
v___y_1555_ = v___y_1546_;
v___y_1556_ = v_snd_1608_;
v___y_1557_ = v___y_1548_;
v___y_1558_ = v___y_1549_;
v___y_1559_ = v___y_1550_;
v___y_1560_ = v___y_1551_;
goto v___jp_1553_;
}
else
{
lean_dec_ref(v_x_1544_);
lean_dec_ref(v_post_1540_);
lean_dec_ref(v_pre_1539_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v___x_1616_, lean_object* v_pre_1617_, lean_object* v_e_1618_, lean_object* v_post_1619_, uint8_t v_usedLetOnly_1620_, uint8_t v_skipConstInApp_1621_, uint8_t v_skipInstances_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Core_checkSystem(v___x_1616_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref_known(v___x_1630_, 1);
lean_inc_ref(v_pre_1617_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc_ref(v_e_1618_);
v___x_1631_ = lean_apply_7(v_pre_1617_, v_e_1618_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, lean_box(0));
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1693_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1693_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1693_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1692_; 
v_fst_1636_ = lean_ctor_get(v_a_1632_, 0);
v_snd_1637_ = lean_ctor_get(v_a_1632_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_a_1632_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1639_ = v_a_1632_;
v_isShared_1640_ = v_isSharedCheck_1692_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snd_1637_);
lean_inc(v_fst_1636_);
lean_dec(v_a_1632_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1692_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___y_1642_; 
switch(lean_obj_tag(v_fst_1636_))
{
case 0:
{
lean_object* v_e_1681_; lean_object* v___x_1683_; 
lean_dec_ref(v_post_1619_);
lean_dec_ref(v_e_1618_);
lean_dec_ref(v_pre_1617_);
v_e_1681_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc_ref(v_e_1681_);
lean_dec_ref_known(v_fst_1636_, 1);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_e_1681_);
v___x_1683_ = v___x_1639_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_e_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_snd_1637_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1683_);
v___x_1685_ = v___x_1634_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
case 1:
{
lean_object* v_e_1688_; lean_object* v___x_1689_; 
lean_del_object(v___x_1639_);
lean_del_object(v___x_1634_);
lean_dec_ref(v_e_1618_);
v_e_1688_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc_ref(v_e_1688_);
lean_dec_ref_known(v_fst_1636_, 1);
v___x_1689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v_e_1688_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1689_;
}
default: 
{
lean_object* v_e_x3f_1690_; 
lean_del_object(v___x_1639_);
lean_del_object(v___x_1634_);
v_e_x3f_1690_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc(v_e_x3f_1690_);
lean_dec_ref_known(v_fst_1636_, 1);
if (lean_obj_tag(v_e_x3f_1690_) == 0)
{
v___y_1642_ = v_e_1618_;
goto v___jp_1641_;
}
else
{
lean_object* v_val_1691_; 
lean_dec_ref(v_e_1618_);
v_val_1691_ = lean_ctor_get(v_e_x3f_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_e_x3f_1690_, 1);
v___y_1642_ = v_val_1691_;
goto v___jp_1641_;
}
}
}
v___jp_1641_:
{
switch(lean_obj_tag(v___y_1642_))
{
case 7:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___x_1643_, v___y_1642_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1644_;
}
case 6:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___x_1645_, v___y_1642_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1646_;
}
case 8:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___x_1647_, v___y_1642_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1648_;
}
case 5:
{
lean_object* v_dummy_1649_; lean_object* v_nargs_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_dummy_1649_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1650_ = l_Lean_Expr_getAppNumArgs(v___y_1642_);
lean_inc(v_nargs_1650_);
v___x_1651_ = lean_mk_array(v_nargs_1650_, v_dummy_1649_);
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_nat_sub(v_nargs_1650_, v___x_1652_);
lean_dec(v_nargs_1650_);
v___x_1654_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1622_, v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v___y_1642_, v___x_1651_, v___x_1653_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1654_;
}
case 10:
{
lean_object* v_data_1655_; lean_object* v_expr_1656_; lean_object* v___x_1657_; 
v_data_1655_ = lean_ctor_get(v___y_1642_, 0);
v_expr_1656_ = lean_ctor_get(v___y_1642_, 1);
lean_inc_ref(v_expr_1656_);
lean_inc_ref(v_post_1619_);
lean_inc_ref(v_pre_1617_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v_expr_1656_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; size_t v___x_1661_; size_t v___x_1662_; uint8_t v___x_1663_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v_fst_1659_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1658_);
v___x_1661_ = lean_ptr_addr(v_expr_1656_);
v___x_1662_ = lean_ptr_addr(v_fst_1659_);
v___x_1663_ = lean_usize_dec_eq(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_inc(v_data_1655_);
lean_dec_ref_known(v___y_1642_, 2);
v___x_1664_ = l_Lean_Expr_mdata___override(v_data_1655_, v_fst_1659_);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___x_1664_, v___y_1623_, v_snd_1660_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_fst_1659_);
v___x_1666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___y_1642_, v___y_1623_, v_snd_1660_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1666_;
}
}
else
{
lean_dec_ref_known(v___y_1642_, 2);
lean_dec_ref(v_post_1619_);
lean_dec_ref(v_pre_1617_);
return v___x_1657_;
}
}
case 11:
{
lean_object* v_typeName_1667_; lean_object* v_idx_1668_; lean_object* v_struct_1669_; lean_object* v___x_1670_; 
v_typeName_1667_ = lean_ctor_get(v___y_1642_, 0);
v_idx_1668_ = lean_ctor_get(v___y_1642_, 1);
v_struct_1669_ = lean_ctor_get(v___y_1642_, 2);
lean_inc_ref(v_struct_1669_);
lean_inc_ref(v_post_1619_);
lean_inc_ref(v_pre_1617_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v_struct_1669_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_fst_1672_; lean_object* v_snd_1673_; size_t v___x_1674_; size_t v___x_1675_; uint8_t v___x_1676_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v_fst_1672_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_fst_1672_);
v_snd_1673_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1673_);
lean_dec(v_a_1671_);
v___x_1674_ = lean_ptr_addr(v_struct_1669_);
v___x_1675_ = lean_ptr_addr(v_fst_1672_);
v___x_1676_ = lean_usize_dec_eq(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_inc(v_idx_1668_);
lean_inc(v_typeName_1667_);
lean_dec_ref_known(v___y_1642_, 3);
v___x_1677_ = l_Lean_Expr_proj___override(v_typeName_1667_, v_idx_1668_, v_fst_1672_);
v___x_1678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___x_1677_, v___y_1623_, v_snd_1673_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
lean_dec(v_fst_1672_);
v___x_1679_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___y_1642_, v___y_1623_, v_snd_1673_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1679_;
}
}
else
{
lean_dec_ref_known(v___y_1642_, 3);
lean_dec_ref(v_post_1619_);
lean_dec_ref(v_pre_1617_);
return v___x_1670_;
}
}
default: 
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1617_, v_post_1619_, v_usedLetOnly_1620_, v_skipConstInApp_1621_, v_skipInstances_1622_, v___y_1642_, v___y_1623_, v_snd_1637_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1680_;
}
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_post_1619_);
lean_dec_ref(v_e_1618_);
lean_dec_ref(v_pre_1617_);
v_a_1694_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1631_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1631_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v___y_1624_);
lean_dec_ref(v_post_1619_);
lean_dec_ref(v_e_1618_);
lean_dec_ref(v_pre_1617_);
v_a_1702_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1630_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1630_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v___x_1710_, lean_object* v_pre_1711_, lean_object* v_e_1712_, lean_object* v_post_1713_, lean_object* v_usedLetOnly_1714_, lean_object* v_skipConstInApp_1715_, lean_object* v_skipInstances_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v_usedLetOnly_boxed_1724_; uint8_t v_skipConstInApp_boxed_1725_; uint8_t v_skipInstances_boxed_1726_; lean_object* v_res_1727_; 
v_usedLetOnly_boxed_1724_ = lean_unbox(v_usedLetOnly_1714_);
v_skipConstInApp_boxed_1725_ = lean_unbox(v_skipConstInApp_1715_);
v_skipInstances_boxed_1726_ = lean_unbox(v_skipInstances_1716_);
v_res_1727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_1710_, v_pre_1711_, v_e_1712_, v_post_1713_, v_usedLetOnly_boxed_1724_, v_skipConstInApp_boxed_1725_, v_skipInstances_boxed_1726_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1717_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1728_, lean_object* v_post_1729_, uint8_t v_usedLetOnly_1730_, uint8_t v_skipConstInApp_1731_, uint8_t v_skipInstances_1732_, lean_object* v_e_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc(v_a_1734_);
v___x_1741_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1741_, 0, lean_box(0));
lean_closure_set(v___x_1741_, 1, lean_box(0));
lean_closure_set(v___x_1741_, 2, v_a_1734_);
v___x_1742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1741_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1797_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1797_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1797_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1796_; 
v_fst_1747_ = lean_ctor_get(v_a_1743_, 0);
v_snd_1748_ = lean_ctor_get(v_a_1743_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1750_ = v_a_1743_;
v_isShared_1751_ = v_isSharedCheck_1796_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_inc(v_fst_1747_);
lean_dec(v_a_1743_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1796_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1747_, v_e_1733_);
lean_dec(v_fst_1747_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; 
lean_del_object(v___x_1750_);
lean_del_object(v___x_1745_);
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0));
v___x_1754_ = lean_box(v_usedLetOnly_1730_);
v___x_1755_ = lean_box(v_skipConstInApp_1731_);
v___x_1756_ = lean_box(v_skipInstances_1732_);
lean_inc_ref(v_e_1733_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1757_, 0, v___x_1753_);
lean_closure_set(v___f_1757_, 1, v_pre_1728_);
lean_closure_set(v___f_1757_, 2, v_e_1733_);
lean_closure_set(v___f_1757_, 3, v_post_1729_);
lean_closure_set(v___f_1757_, 4, v___x_1754_);
lean_closure_set(v___f_1757_, 5, v___x_1755_);
lean_closure_set(v___f_1757_, 6, v___x_1756_);
v___x_1758_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1757_, v_a_1734_, v_snd_1748_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_fst_1760_ = lean_ctor_get(v_a_1759_, 0);
lean_inc_n(v_fst_1760_, 2);
v_snd_1761_ = lean_ctor_get(v_a_1759_, 1);
lean_inc(v_snd_1761_);
lean_dec(v_a_1759_);
lean_inc(v_a_1734_);
v___f_1762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1762_, 0, v_a_1734_);
lean_closure_set(v___f_1762_, 1, v_e_1733_);
lean_closure_set(v___f_1762_, 2, v_fst_1760_);
v___x_1763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1762_, v_snd_1761_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1780_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1780_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1780_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_snd_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1778_; 
v_snd_1768_ = lean_ctor_get(v_a_1764_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_a_1764_, 0);
lean_dec(v_unused_1779_);
v___x_1770_ = v_a_1764_;
v_isShared_1771_ = v_isSharedCheck_1778_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_snd_1768_);
lean_dec(v_a_1764_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1778_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_fst_1760_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fst_1760_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_snd_1768_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1773_);
v___x_1775_ = v___x_1766_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_fst_1760_);
v_a_1781_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1763_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1763_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_dec_ref(v_e_1733_);
return v___x_1758_;
}
}
else
{
lean_object* v_val_1789_; lean_object* v___x_1791_; 
lean_dec_ref(v_e_1733_);
lean_dec_ref(v_post_1729_);
lean_dec_ref(v_pre_1728_);
v_val_1789_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1752_, 1);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v_val_1789_);
v___x_1791_ = v___x_1750_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_val_1789_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_snd_1748_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1791_);
v___x_1793_ = v___x_1745_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v_e_1733_);
lean_dec_ref(v_post_1729_);
lean_dec_ref(v_pre_1728_);
v_a_1798_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1742_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1742_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1806_, lean_object* v_pre_1807_, lean_object* v_post_1808_, lean_object* v_usedLetOnly_1809_, lean_object* v_skipConstInApp_1810_, lean_object* v_skipInstances_1811_, lean_object* v_body_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v_usedLetOnly_boxed_1821_; uint8_t v_skipConstInApp_boxed_1822_; uint8_t v_skipInstances_boxed_1823_; lean_object* v_res_1824_; 
v_usedLetOnly_boxed_1821_ = lean_unbox(v_usedLetOnly_1809_);
v_skipConstInApp_boxed_1822_ = lean_unbox(v_skipConstInApp_1810_);
v_skipInstances_boxed_1823_ = lean_unbox(v_skipInstances_1811_);
v_res_1824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1806_, v_pre_1807_, v_post_1808_, v_usedLetOnly_boxed_1821_, v_skipConstInApp_boxed_1822_, v_skipInstances_boxed_1823_, v_body_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1814_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1825_, lean_object* v_post_1826_, uint8_t v_usedLetOnly_1827_, uint8_t v_skipConstInApp_1828_, uint8_t v_skipInstances_1829_, lean_object* v_fvars_1830_, lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
if (lean_obj_tag(v_e_1831_) == 7)
{
lean_object* v_binderName_1839_; lean_object* v_binderType_1840_; lean_object* v_body_1841_; uint8_t v_binderInfo_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_binderName_1839_ = lean_ctor_get(v_e_1831_, 0);
lean_inc(v_binderName_1839_);
v_binderType_1840_ = lean_ctor_get(v_e_1831_, 1);
lean_inc_ref(v_binderType_1840_);
v_body_1841_ = lean_ctor_get(v_e_1831_, 2);
lean_inc_ref(v_body_1841_);
v_binderInfo_1842_ = lean_ctor_get_uint8(v_e_1831_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1831_, 3);
v___x_1843_ = lean_expr_instantiate_rev(v_binderType_1840_, v_fvars_1830_);
lean_dec_ref(v_binderType_1840_);
lean_inc_ref(v_post_1826_);
lean_inc_ref(v_pre_1825_);
v___x_1844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1825_, v_post_1826_, v_usedLetOnly_1827_, v_skipConstInApp_1828_, v_skipInstances_1829_, v___x_1843_, v_a_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___f_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_fst_1846_ = lean_ctor_get(v_a_1845_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v_a_1845_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_a_1845_);
v___x_1848_ = lean_box(v_usedLetOnly_1827_);
v___x_1849_ = lean_box(v_skipConstInApp_1828_);
v___x_1850_ = lean_box(v_skipInstances_1829_);
v___f_1851_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1851_, 0, v_fvars_1830_);
lean_closure_set(v___f_1851_, 1, v_pre_1825_);
lean_closure_set(v___f_1851_, 2, v_post_1826_);
lean_closure_set(v___f_1851_, 3, v___x_1848_);
lean_closure_set(v___f_1851_, 4, v___x_1849_);
lean_closure_set(v___f_1851_, 5, v___x_1850_);
lean_closure_set(v___f_1851_, 6, v_body_1841_);
v___x_1852_ = 0;
v___x_1853_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1839_, v_binderInfo_1842_, v_fst_1846_, v___f_1851_, v___x_1852_, v_a_1832_, v_snd_1847_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1853_;
}
else
{
lean_dec_ref(v_body_1841_);
lean_dec(v_binderName_1839_);
lean_dec_ref(v_fvars_1830_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
return v___x_1844_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_expr_instantiate_rev(v_e_1831_, v_fvars_1830_);
lean_dec_ref(v_e_1831_);
lean_inc_ref(v_post_1826_);
lean_inc_ref(v_pre_1825_);
v___x_1855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1825_, v_post_1826_, v_usedLetOnly_1827_, v_skipConstInApp_1828_, v_skipInstances_1829_, v___x_1854_, v_a_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; uint8_t v___x_1859_; uint8_t v___x_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v_fst_1857_ = lean_ctor_get(v_a_1856_, 0);
lean_inc(v_fst_1857_);
v_snd_1858_ = lean_ctor_get(v_a_1856_, 1);
lean_inc(v_snd_1858_);
lean_dec(v_a_1856_);
v___x_1859_ = 0;
v___x_1860_ = 1;
v___x_1861_ = 1;
v___x_1862_ = l_Lean_Meta_mkForallFVars(v_fvars_1830_, v_fst_1857_, v___x_1859_, v_usedLetOnly_1827_, v___x_1860_, v___x_1861_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec_ref(v_fvars_1830_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1825_, v_post_1826_, v_usedLetOnly_1827_, v_skipConstInApp_1828_, v_skipInstances_1829_, v_a_1863_, v_a_1832_, v_snd_1858_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1864_;
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_snd_1858_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
v_a_1865_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1862_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1862_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1830_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1873_, lean_object* v_pre_1874_, lean_object* v_post_1875_, uint8_t v_usedLetOnly_1876_, uint8_t v_skipConstInApp_1877_, uint8_t v_skipInstances_1878_, lean_object* v_body_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_array_push(v_fvars_1873_, v_x_1880_);
v___x_1889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1874_, v_post_1875_, v_usedLetOnly_1876_, v_skipConstInApp_1877_, v_skipInstances_1878_, v___x_1888_, v_body_1879_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1890_, lean_object* v_post_1891_, lean_object* v_usedLetOnly_1892_, lean_object* v_skipConstInApp_1893_, lean_object* v_skipInstances_1894_, lean_object* v_sz_1895_, lean_object* v_i_1896_, lean_object* v_bs_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v_usedLetOnly_boxed_1905_; uint8_t v_skipConstInApp_boxed_1906_; uint8_t v_skipInstances_boxed_1907_; size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_usedLetOnly_boxed_1905_ = lean_unbox(v_usedLetOnly_1892_);
v_skipConstInApp_boxed_1906_ = lean_unbox(v_skipConstInApp_1893_);
v_skipInstances_boxed_1907_ = lean_unbox(v_skipInstances_1894_);
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1895_);
lean_dec(v_sz_1895_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1890_, v_post_1891_, v_usedLetOnly_boxed_1905_, v_skipConstInApp_boxed_1906_, v_skipInstances_boxed_1907_, v_sz_boxed_1908_, v_i_boxed_1909_, v_bs_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1898_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1911_, lean_object* v_post_1912_, lean_object* v_usedLetOnly_1913_, lean_object* v_skipConstInApp_1914_, lean_object* v_skipInstances_1915_, lean_object* v_e_1916_, lean_object* v_a_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
uint8_t v_usedLetOnly_boxed_1924_; uint8_t v_skipConstInApp_boxed_1925_; uint8_t v_skipInstances_boxed_1926_; lean_object* v_res_1927_; 
v_usedLetOnly_boxed_1924_ = lean_unbox(v_usedLetOnly_1913_);
v_skipConstInApp_boxed_1925_ = lean_unbox(v_skipConstInApp_1914_);
v_skipInstances_boxed_1926_ = lean_unbox(v_skipInstances_1915_);
v_res_1927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1911_, v_post_1912_, v_usedLetOnly_boxed_1924_, v_skipConstInApp_boxed_1925_, v_skipInstances_boxed_1926_, v_e_1916_, v_a_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v_a_1917_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1928_, lean_object* v_post_1929_, lean_object* v_usedLetOnly_1930_, lean_object* v_skipConstInApp_1931_, lean_object* v_skipInstances_1932_, lean_object* v_fvars_1933_, lean_object* v_e_1934_, lean_object* v_a_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
uint8_t v_usedLetOnly_boxed_1942_; uint8_t v_skipConstInApp_boxed_1943_; uint8_t v_skipInstances_boxed_1944_; lean_object* v_res_1945_; 
v_usedLetOnly_boxed_1942_ = lean_unbox(v_usedLetOnly_1930_);
v_skipConstInApp_boxed_1943_ = lean_unbox(v_skipConstInApp_1931_);
v_skipInstances_boxed_1944_ = lean_unbox(v_skipInstances_1932_);
v_res_1945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1928_, v_post_1929_, v_usedLetOnly_boxed_1942_, v_skipConstInApp_boxed_1943_, v_skipInstances_boxed_1944_, v_fvars_1933_, v_e_1934_, v_a_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v_a_1935_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1946_, lean_object* v_post_1947_, lean_object* v_usedLetOnly_1948_, lean_object* v_skipConstInApp_1949_, lean_object* v_skipInstances_1950_, lean_object* v_fvars_1951_, lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v_usedLetOnly_boxed_1960_; uint8_t v_skipConstInApp_boxed_1961_; uint8_t v_skipInstances_boxed_1962_; lean_object* v_res_1963_; 
v_usedLetOnly_boxed_1960_ = lean_unbox(v_usedLetOnly_1948_);
v_skipConstInApp_boxed_1961_ = lean_unbox(v_skipConstInApp_1949_);
v_skipInstances_boxed_1962_ = lean_unbox(v_skipInstances_1950_);
v_res_1963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1946_, v_post_1947_, v_usedLetOnly_boxed_1960_, v_skipConstInApp_boxed_1961_, v_skipInstances_boxed_1962_, v_fvars_1951_, v_e_1952_, v_a_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v_a_1953_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1964_, lean_object* v_post_1965_, lean_object* v_usedLetOnly_1966_, lean_object* v_skipConstInApp_1967_, lean_object* v_skipInstances_1968_, lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
uint8_t v_usedLetOnly_boxed_1977_; uint8_t v_skipConstInApp_boxed_1978_; uint8_t v_skipInstances_boxed_1979_; lean_object* v_res_1980_; 
v_usedLetOnly_boxed_1977_ = lean_unbox(v_usedLetOnly_1966_);
v_skipConstInApp_boxed_1978_ = lean_unbox(v_skipConstInApp_1967_);
v_skipInstances_boxed_1979_ = lean_unbox(v_skipInstances_1968_);
v_res_1980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1964_, v_post_1965_, v_usedLetOnly_boxed_1977_, v_skipConstInApp_boxed_1978_, v_skipInstances_boxed_1979_, v_e_1969_, v_a_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v_a_1970_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1981_, lean_object* v_post_1982_, lean_object* v_usedLetOnly_1983_, lean_object* v_skipConstInApp_1984_, lean_object* v_skipInstances_1985_, lean_object* v_fvars_1986_, lean_object* v_e_1987_, lean_object* v_a_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
uint8_t v_usedLetOnly_boxed_1995_; uint8_t v_skipConstInApp_boxed_1996_; uint8_t v_skipInstances_boxed_1997_; lean_object* v_res_1998_; 
v_usedLetOnly_boxed_1995_ = lean_unbox(v_usedLetOnly_1983_);
v_skipConstInApp_boxed_1996_ = lean_unbox(v_skipConstInApp_1984_);
v_skipInstances_boxed_1997_ = lean_unbox(v_skipInstances_1985_);
v_res_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1981_, v_post_1982_, v_usedLetOnly_boxed_1995_, v_skipConstInApp_boxed_1996_, v_skipInstances_boxed_1997_, v_fvars_1986_, v_e_1987_, v_a_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v_a_1988_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_1999_, lean_object* v___x_2000_, lean_object* v_pre_2001_, lean_object* v_post_2002_, lean_object* v_usedLetOnly_2003_, lean_object* v_skipConstInApp_2004_, lean_object* v_skipInstances_2005_, lean_object* v_a_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_usedLetOnly_boxed_2015_; uint8_t v_skipConstInApp_boxed_2016_; uint8_t v_skipInstances_boxed_2017_; lean_object* v_res_2018_; 
v_usedLetOnly_boxed_2015_ = lean_unbox(v_usedLetOnly_2003_);
v_skipConstInApp_boxed_2016_ = lean_unbox(v_skipConstInApp_2004_);
v_skipInstances_boxed_2017_ = lean_unbox(v_skipInstances_2005_);
v_res_2018_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1999_, v___x_2000_, v_pre_2001_, v_post_2002_, v_usedLetOnly_boxed_2015_, v_skipConstInApp_boxed_2016_, v_skipInstances_boxed_2017_, v_a_2006_, v_b_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2008_);
lean_dec_ref(v___x_2000_);
lean_dec(v_upperBound_1999_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2019_, lean_object* v_pre_2020_, lean_object* v_post_2021_, lean_object* v_usedLetOnly_2022_, lean_object* v_skipConstInApp_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v_skipInstances_boxed_2034_; uint8_t v_usedLetOnly_boxed_2035_; uint8_t v_skipConstInApp_boxed_2036_; lean_object* v_res_2037_; 
v_skipInstances_boxed_2034_ = lean_unbox(v_skipInstances_2019_);
v_usedLetOnly_boxed_2035_ = lean_unbox(v_usedLetOnly_2022_);
v_skipConstInApp_boxed_2036_ = lean_unbox(v_skipConstInApp_2023_);
v_res_2037_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2034_, v_pre_2020_, v_post_2021_, v_usedLetOnly_boxed_2035_, v_skipConstInApp_boxed_2036_, v_x_2024_, v_x_2025_, v_x_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2027_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_apply_1(v_x_2039_, lean_box(0));
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v___y_2040_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2049_, v_x_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2057_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_unsigned_to_nat(16u);
v___x_2060_ = lean_mk_array(v___x_2059_, v___x_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___x_2061_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2065_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2065_, 0, lean_box(0));
lean_closure_set(v___x_2065_, 1, lean_box(0));
lean_closure_set(v___x_2065_, 2, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2066_, lean_object* v_pre_2067_, lean_object* v_post_2068_, uint8_t v_usedLetOnly_2069_, uint8_t v_skipConstInApp_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2077_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2078_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2077_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
v_fst_2080_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_fst_2080_);
v_snd_2081_ = lean_ctor_get(v_a_2079_, 1);
lean_inc(v_snd_2081_);
lean_dec(v_a_2079_);
v___x_2082_ = 0;
v___x_2083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2067_, v_post_2068_, v_usedLetOnly_2069_, v_skipConstInApp_2070_, v___x_2082_, v_input_2066_, v_fst_2080_, v_snd_2081_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v_fst_2085_; lean_object* v_snd_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2105_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v_fst_2085_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_fst_2085_);
v_snd_2086_ = lean_ctor_get(v_a_2084_, 1);
lean_inc(v_snd_2086_);
lean_dec(v_a_2084_);
v___x_2087_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2087_, 0, lean_box(0));
lean_closure_set(v___x_2087_, 1, lean_box(0));
lean_closure_set(v___x_2087_, 2, v_fst_2080_);
v___x_2088_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2087_, v_snd_2086_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2105_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2105_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_snd_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2103_; 
v_snd_2093_ = lean_ctor_get(v_a_2089_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_a_2089_, 0);
lean_dec(v_unused_2104_);
v___x_2095_ = v_a_2089_;
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_snd_2093_);
lean_dec(v_a_2089_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v_fst_2085_);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_fst_2085_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_snd_2093_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2098_);
v___x_2100_ = v___x_2091_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
else
{
lean_dec(v_fst_2080_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2106_, lean_object* v_pre_2107_, lean_object* v_post_2108_, lean_object* v_usedLetOnly_2109_, lean_object* v_skipConstInApp_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_usedLetOnly_boxed_2117_; uint8_t v_skipConstInApp_boxed_2118_; lean_object* v_res_2119_; 
v_usedLetOnly_boxed_2117_ = lean_unbox(v_usedLetOnly_2109_);
v_skipConstInApp_boxed_2118_ = lean_unbox(v_skipConstInApp_2110_);
v_res_2119_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2106_, v_pre_2107_, v_post_2108_, v_usedLetOnly_boxed_2117_, v_skipConstInApp_boxed_2118_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_keyedConfig_2128_; uint8_t v_trackZetaDelta_2129_; lean_object* v_zetaDeltaSet_2130_; lean_object* v_lctx_2131_; lean_object* v_localInstances_2132_; lean_object* v_defEqCtx_x3f_2133_; lean_object* v_synthPendingDepth_2134_; lean_object* v_customCanUnfoldPredicate_x3f_2135_; uint8_t v_univApprox_2136_; uint8_t v_inTypeClassResolution_2137_; uint8_t v_cacheInferType_2138_; lean_object* v___f_2139_; lean_object* v___f_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_keyedConfig_2128_ = lean_ctor_get(v_a_2123_, 0);
v_trackZetaDelta_2129_ = lean_ctor_get_uint8(v_a_2123_, sizeof(void*)*7);
v_zetaDeltaSet_2130_ = lean_ctor_get(v_a_2123_, 1);
v_lctx_2131_ = lean_ctor_get(v_a_2123_, 2);
v_localInstances_2132_ = lean_ctor_get(v_a_2123_, 3);
v_defEqCtx_x3f_2133_ = lean_ctor_get(v_a_2123_, 4);
v_synthPendingDepth_2134_ = lean_ctor_get(v_a_2123_, 5);
v_customCanUnfoldPredicate_x3f_2135_ = lean_ctor_get(v_a_2123_, 6);
v_univApprox_2136_ = lean_ctor_get_uint8(v_a_2123_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2137_ = lean_ctor_get_uint8(v_a_2123_, sizeof(void*)*7 + 2);
v_cacheInferType_2138_ = lean_ctor_get_uint8(v_a_2123_, sizeof(void*)*7 + 3);
v___f_2139_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2140_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2141_ = 0;
v___x_2142_ = 3;
v___x_2143_ = lean_box(0);
lean_inc_ref(v_keyedConfig_2128_);
v___x_2144_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2142_, v_keyedConfig_2128_);
lean_inc(v_customCanUnfoldPredicate_x3f_2135_);
lean_inc(v_synthPendingDepth_2134_);
lean_inc(v_defEqCtx_x3f_2133_);
lean_inc_ref(v_localInstances_2132_);
lean_inc_ref(v_lctx_2131_);
lean_inc(v_zetaDeltaSet_2130_);
v___x_2145_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_zetaDeltaSet_2130_);
lean_ctor_set(v___x_2145_, 2, v_lctx_2131_);
lean_ctor_set(v___x_2145_, 3, v_localInstances_2132_);
lean_ctor_set(v___x_2145_, 4, v_defEqCtx_x3f_2133_);
lean_ctor_set(v___x_2145_, 5, v_synthPendingDepth_2134_);
lean_ctor_set(v___x_2145_, 6, v_customCanUnfoldPredicate_x3f_2135_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*7, v_trackZetaDelta_2129_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*7 + 1, v_univApprox_2136_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2137_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*7 + 3, v_cacheInferType_2138_);
v___x_2146_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2122_, v___f_2140_, v___f_2139_, v___x_2141_, v___x_2141_, v___x_2143_, v___x_2145_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec_ref_known(v___x_2145_, 7);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Meta_expandCoe(v_e_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2154_, lean_object* v_m_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2155_, v_a_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_m_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2158_, v_m_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_m_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2163_, v_x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2166_, v_x_2167_, v_x_2168_);
lean_dec_ref(v_x_2168_);
lean_dec_ref(v_x_2167_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2171_, lean_object* v_a_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_a_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2175_, v_a_2176_, v_x_2177_);
lean_dec(v_x_2177_);
lean_dec(v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2179_, lean_object* v___x_2180_, lean_object* v_pre_2181_, lean_object* v_post_2182_, uint8_t v_usedLetOnly_2183_, uint8_t v_skipConstInApp_2184_, uint8_t v_skipInstances_2185_, lean_object* v___x_2186_, lean_object* v_inst_2187_, lean_object* v_R_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_, lean_object* v_c_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2179_, v___x_2180_, v_pre_2181_, v_post_2182_, v_usedLetOnly_2183_, v_skipConstInApp_2184_, v_skipInstances_2185_, v_a_2189_, v_b_2190_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2200_ = _args[0];
lean_object* v___x_2201_ = _args[1];
lean_object* v_pre_2202_ = _args[2];
lean_object* v_post_2203_ = _args[3];
lean_object* v_usedLetOnly_2204_ = _args[4];
lean_object* v_skipConstInApp_2205_ = _args[5];
lean_object* v_skipInstances_2206_ = _args[6];
lean_object* v___x_2207_ = _args[7];
lean_object* v_inst_2208_ = _args[8];
lean_object* v_R_2209_ = _args[9];
lean_object* v_a_2210_ = _args[10];
lean_object* v_b_2211_ = _args[11];
lean_object* v_c_2212_ = _args[12];
lean_object* v___y_2213_ = _args[13];
lean_object* v___y_2214_ = _args[14];
lean_object* v___y_2215_ = _args[15];
lean_object* v___y_2216_ = _args[16];
lean_object* v___y_2217_ = _args[17];
lean_object* v___y_2218_ = _args[18];
lean_object* v___y_2219_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2220_; uint8_t v_skipConstInApp_boxed_2221_; uint8_t v_skipInstances_boxed_2222_; lean_object* v_res_2223_; 
v_usedLetOnly_boxed_2220_ = lean_unbox(v_usedLetOnly_2204_);
v_skipConstInApp_boxed_2221_ = lean_unbox(v_skipConstInApp_2205_);
v_skipInstances_boxed_2222_ = lean_unbox(v_skipInstances_2206_);
v_res_2223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2200_, v___x_2201_, v_pre_2202_, v_post_2203_, v_usedLetOnly_boxed_2220_, v_skipConstInApp_boxed_2221_, v_skipInstances_boxed_2222_, v___x_2207_, v_inst_2208_, v_R_2209_, v_a_2210_, v_b_2211_, v_c_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2213_);
lean_dec(v___x_2207_);
lean_dec_ref(v___x_2201_);
lean_dec(v_upperBound_2200_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2224_, lean_object* v_m_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2225_, v_a_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2228_, lean_object* v_m_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2228_, v_m_2229_, v_a_2230_);
lean_dec_ref(v_a_2230_);
lean_dec_ref(v_m_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2232_, lean_object* v_name_2233_, uint8_t v_bi_2234_, lean_object* v_type_2235_, lean_object* v_k_2236_, uint8_t v_kind_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2233_, v_bi_2234_, v_type_2235_, v_k_2236_, v_kind_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_name_2247_, lean_object* v_bi_2248_, lean_object* v_type_2249_, lean_object* v_k_2250_, lean_object* v_kind_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v_bi_boxed_2259_; uint8_t v_kind_boxed_2260_; lean_object* v_res_2261_; 
v_bi_boxed_2259_ = lean_unbox(v_bi_2248_);
v_kind_boxed_2260_ = lean_unbox(v_kind_2251_);
v_res_2261_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2246_, v_name_2247_, v_bi_boxed_2259_, v_type_2249_, v_k_2250_, v_kind_boxed_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2252_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2262_, lean_object* v_name_2263_, lean_object* v_type_2264_, lean_object* v_val_2265_, lean_object* v_k_2266_, uint8_t v_nondep_2267_, uint8_t v_kind_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2263_, v_type_2264_, v_val_2265_, v_k_2266_, v_nondep_2267_, v_kind_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2277_, lean_object* v_name_2278_, lean_object* v_type_2279_, lean_object* v_val_2280_, lean_object* v_k_2281_, lean_object* v_nondep_2282_, lean_object* v_kind_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_nondep_boxed_2291_; uint8_t v_kind_boxed_2292_; lean_object* v_res_2293_; 
v_nondep_boxed_2291_ = lean_unbox(v_nondep_2282_);
v_kind_boxed_2292_ = lean_unbox(v_kind_2283_);
v_res_2293_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2277_, v_name_2278_, v_type_2279_, v_val_2280_, v_k_2281_, v_nondep_boxed_2291_, v_kind_boxed_2292_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2284_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2294_, lean_object* v_ref_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2295_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_ref_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2302_, v_ref_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2320_, lean_object* v_x_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2320_, v_x_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2322_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2330_, lean_object* v_m_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2331_, v_a_2332_, v_b_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2335_, lean_object* v_x_2336_, size_t v_x_2337_, lean_object* v_x_2338_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2336_, v_x_2337_, v_x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
size_t v_x_40066__boxed_2344_; uint8_t v_res_2345_; lean_object* v_r_2346_; 
v_x_40066__boxed_2344_ = lean_unbox_usize(v_x_2342_);
lean_dec(v_x_2342_);
v_res_2345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2340_, v_x_2341_, v_x_40066__boxed_2344_, v_x_2343_);
lean_dec_ref(v_x_2343_);
lean_dec_ref(v_x_2341_);
v_r_2346_ = lean_box(v_res_2345_);
return v_r_2346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2347_, lean_object* v_a_2348_, lean_object* v_x_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2348_, v_x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2351_, lean_object* v_a_2352_, lean_object* v_x_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2351_, v_a_2352_, v_x_2353_);
lean_dec(v_x_2353_);
lean_dec_ref(v_a_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2355_, lean_object* v_a_2356_, lean_object* v_x_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2356_, v_x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_a_2360_, lean_object* v_x_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2359_, v_a_2360_, v_x_2361_);
lean_dec(v_x_2361_);
lean_dec_ref(v_a_2360_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2364_, lean_object* v_data_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2367_, lean_object* v_a_2368_, lean_object* v_b_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2368_, v_b_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_heq_2375_, lean_object* v_i_2376_, lean_object* v_k_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2373_, v_i_2376_, v_k_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_keys_2380_, lean_object* v_vals_2381_, lean_object* v_heq_2382_, lean_object* v_i_2383_, lean_object* v_k_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2379_, v_keys_2380_, v_vals_2381_, v_heq_2382_, v_i_2383_, v_k_2384_);
lean_dec_ref(v_k_2384_);
lean_dec_ref(v_vals_2381_);
lean_dec_ref(v_keys_2380_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2387_, lean_object* v_i_2388_, lean_object* v_source_2389_, lean_object* v_target_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2388_, v_source_2389_, v_target_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2393_, v_x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2396_, lean_object* v_decl_2397_, lean_object* v_ref_2398_){
_start:
{
lean_object* v_defValue_2400_; lean_object* v_descr_2401_; lean_object* v_deprecation_x3f_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_defValue_2400_ = lean_ctor_get(v_decl_2397_, 0);
v_descr_2401_ = lean_ctor_get(v_decl_2397_, 1);
v_deprecation_x3f_2402_ = lean_ctor_get(v_decl_2397_, 2);
v___x_2403_ = lean_alloc_ctor(1, 0, 1);
v___x_2404_ = lean_unbox(v_defValue_2400_);
lean_ctor_set_uint8(v___x_2403_, 0, v___x_2404_);
lean_inc(v_deprecation_x3f_2402_);
lean_inc_ref(v_descr_2401_);
lean_inc_n(v_name_2396_, 2);
v___x_2405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2405_, 0, v_name_2396_);
lean_ctor_set(v___x_2405_, 1, v_ref_2398_);
lean_ctor_set(v___x_2405_, 2, v___x_2403_);
lean_ctor_set(v___x_2405_, 3, v_descr_2401_);
lean_ctor_set(v___x_2405_, 4, v_deprecation_x3f_2402_);
v___x_2406_ = lean_register_option(v_name_2396_, v___x_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2414_; 
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v___x_2406_, 0);
lean_dec(v_unused_2415_);
v___x_2408_ = v___x_2406_;
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v___x_2406_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2414_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_inc(v_defValue_2400_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_name_2396_);
lean_ctor_set(v___x_2410_, 1, v_defValue_2400_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2410_);
v___x_2412_ = v___x_2408_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_name_2396_);
v_a_2416_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2406_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2406_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2424_, lean_object* v_decl_2425_, lean_object* v_ref_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2424_, v_decl_2425_, v_ref_2426_);
lean_dec_ref(v_decl_2425_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2446_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2443_, v___x_2444_, v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_ref_2455_; lean_object* v___x_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v_ref_2455_ = lean_ctor_get(v___y_2452_, 5);
v___x_2456_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_inc(v_ref_2455_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_ref_2455_);
lean_ctor_set(v___x_2461_, 1, v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set_tag(v___x_2459_, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2472_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2484_ = l_Lean_stringToMessageData(v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2488_, lean_object* v_expectedType_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; 
lean_inc(v_a_2493_);
lean_inc_ref(v_a_2492_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
lean_inc_ref(v_expr_2488_);
v___x_2495_ = lean_infer_type(v_expr_2488_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc_n(v_a_2496_, 2);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l_Lean_Meta_getLevel(v_a_2496_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
lean_inc_ref(v_expectedType_2489_);
v___x_2499_ = l_Lean_Meta_getLevel(v_expectedType_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2500_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2498_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
lean_inc_ref(v___x_2504_);
v___x_2505_ = l_Lean_mkConst(v___x_2501_, v___x_2504_);
v___x_2506_ = lean_unsigned_to_nat(3u);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2506_);
lean_inc(v_a_2496_);
v___x_2508_ = lean_array_push(v___x_2507_, v_a_2496_);
lean_inc_ref(v_expr_2488_);
v___x_2509_ = lean_array_push(v___x_2508_, v_expr_2488_);
lean_inc_ref(v_expectedType_2489_);
v___x_2510_ = lean_array_push(v___x_2509_, v_expectedType_2489_);
v___x_2511_ = l_Lean_mkAppN(v___x_2505_, v___x_2510_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = lean_box(0);
v___x_2513_ = l_Lean_Meta_trySynthInstance(v___x_2511_, v___x_2512_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2611_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2611_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2611_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
switch(lean_obj_tag(v_a_2514_))
{
case 0:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_dec_ref_known(v___x_2504_, 2);
lean_dec(v_a_2496_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v___x_2518_ = lean_box(0);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
case 1:
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2606_; 
lean_del_object(v___x_2516_);
v_a_2522_ = lean_ctor_get(v_a_2514_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2514_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2524_ = v_a_2514_;
v_isShared_2525_ = v_isSharedCheck_2606_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v_a_2514_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2606_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2526_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2527_ = l_Lean_mkConst(v___x_2526_, v___x_2504_);
v___x_2528_ = lean_unsigned_to_nat(4u);
v___x_2529_ = lean_mk_empty_array_with_capacity(v___x_2528_);
v___x_2530_ = lean_array_push(v___x_2529_, v_a_2496_);
lean_inc_ref(v_expr_2488_);
v___x_2531_ = lean_array_push(v___x_2530_, v_expr_2488_);
lean_inc_ref(v_expectedType_2489_);
v___x_2532_ = lean_array_push(v___x_2531_, v_expectedType_2489_);
v___x_2533_ = lean_array_push(v___x_2532_, v_a_2522_);
v___x_2534_ = l_Lean_mkAppN(v___x_2527_, v___x_2533_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = l_Lean_Meta_expandCoe(v___x_2534_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2597_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2597_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2597_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_fst_2547_; lean_object* v___x_2548_; 
v_fst_2547_ = lean_ctor_get(v_a_2536_, 0);
lean_inc(v_a_2493_);
lean_inc_ref(v_a_2492_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
lean_inc(v_fst_2547_);
v___x_2548_ = lean_infer_type(v_fst_2547_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
lean_inc_ref(v_expectedType_2489_);
v___x_2550_ = l_Lean_Meta_isExprDefEq(v_a_2549_, v_expectedType_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; uint8_t v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2578_; 
lean_inc(v_fst_2547_);
lean_del_object(v___x_2538_);
lean_del_object(v___x_2524_);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_a_2536_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; lean_object* v_unused_2580_; 
v_unused_2579_ = lean_ctor_get(v_a_2536_, 1);
lean_dec(v_unused_2579_);
v_unused_2580_ = lean_ctor_get(v_a_2536_, 0);
lean_dec(v_unused_2580_);
v___x_2554_ = v_a_2536_;
v_isShared_2555_ = v_isSharedCheck_2578_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v_a_2536_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2578_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2556_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2557_ = l_Lean_indentExpr(v_expr_2488_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 7);
lean_ctor_set(v___x_2554_, 1, v___x_2557_);
lean_ctor_set(v___x_2554_, 0, v___x_2556_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v___x_2560_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_indentExpr(v_expectedType_2489_);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l_Lean_indentExpr(v_fst_2547_);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2567_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
goto v___jp_2540_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_del_object(v___x_2538_);
lean_dec(v_a_2536_);
lean_del_object(v___x_2524_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2581_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2550_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2550_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2538_);
lean_dec(v_a_2536_);
lean_del_object(v___x_2524_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2589_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2548_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2548_);
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
v___jp_2540_:
{
lean_object* v___x_2542_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_a_2536_);
v___x_2542_ = v___x_2524_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2536_);
v___x_2542_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2542_);
v___x_2544_ = v___x_2538_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2524_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2598_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2535_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2535_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
default: 
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec_ref_known(v___x_2504_, 2);
lean_dec(v_a_2496_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v___x_2607_ = lean_box(2);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2607_);
v___x_2609_ = v___x_2516_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref_known(v___x_2504_, 2);
lean_dec(v_a_2496_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2612_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2513_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2513_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
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
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_a_2498_);
lean_dec(v_a_2496_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2620_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2499_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2499_);
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
lean_dec(v_a_2496_);
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2628_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2497_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2497_);
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
lean_dec_ref(v_expectedType_2489_);
lean_dec_ref(v_expr_2488_);
v_a_2636_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2495_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2495_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2644_, lean_object* v_expectedType_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2644_, v_expectedType_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2652_, lean_object* v_msg_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2660_, v_msg_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2668_, lean_object* v_expectedType_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2668_, v_expectedType_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2700_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2700_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2700_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
switch(lean_obj_tag(v_a_2676_))
{
case 0:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_box(0);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
case 1:
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2695_; 
v_a_2684_ = lean_ctor_get(v_a_2676_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2676_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2686_ = v_a_2676_;
v_isShared_2687_ = v_isSharedCheck_2695_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v_a_2676_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2695_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_fst_2688_; lean_object* v___x_2690_; 
v_fst_2688_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_fst_2688_);
lean_dec(v_a_2684_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v_fst_2688_);
v___x_2690_ = v___x_2686_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_fst_2688_);
v___x_2690_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2690_);
v___x_2692_ = v___x_2678_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
default: 
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_box(2);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2696_);
v___x_2698_ = v___x_2678_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_a_2701_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2675_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2675_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2709_, lean_object* v_expectedType_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2709_, v_expectedType_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2716_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2738_; 
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
lean_inc_ref(v_expr_2732_);
v___x_2738_ = lean_infer_type(v_expr_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_n(v_a_2739_, 2);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2740_ = l_Lean_Meta_getLevel(v_a_2739_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc_n(v_a_2743_, 2);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = l_Lean_mkSort(v_a_2743_);
lean_inc(v_a_2739_);
v___x_2745_ = l_Lean_mkArrow(v_a_2739_, v___x_2744_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2746_);
v___x_2748_ = 0;
v___x_2749_ = lean_box(0);
v___x_2750_ = l_Lean_Meta_mkFreshExprMVar(v___x_2747_, v___x_2748_, v___x_2749_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc_n(v_a_2751_, 2);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2743_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2741_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_inc_ref(v___x_2755_);
v___x_2756_ = l_Lean_Expr_const___override(v___x_2752_, v___x_2755_);
lean_inc(v_a_2739_);
v___x_2757_ = l_Lean_mkAppB(v___x_2756_, v_a_2739_, v_a_2751_);
v___x_2758_ = lean_box(0);
v___x_2759_ = l_Lean_Meta_trySynthInstance(v___x_2757_, v___x_2758_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2846_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2846_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2846_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2762_);
v_a_2764_ = lean_ctor_get(v_a_2760_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2766_ = v_a_2760_;
v_isShared_2767_ = v_isSharedCheck_2842_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v_a_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2842_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2768_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2769_ = l_Lean_Expr_const___override(v___x_2768_, v___x_2755_);
lean_inc_ref(v_expr_2732_);
lean_inc(v_a_2764_);
v___x_2770_ = l_Lean_mkApp4(v___x_2769_, v_a_2739_, v_a_2751_, v_a_2764_, v_expr_2732_);
v___x_2771_ = l_Lean_Meta_expandCoe(v___x_2770_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2833_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2833_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2833_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_fst_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2831_; 
v_fst_2776_ = lean_ctor_get(v_a_2772_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_a_2772_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v_a_2772_, 1);
lean_dec(v_unused_2832_);
v___x_2778_ = v_a_2772_;
v_isShared_2779_ = v_isSharedCheck_2831_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_fst_2776_);
lean_dec(v_a_2772_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2831_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2787_; 
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
lean_inc(v_fst_2776_);
v___x_2787_ = lean_infer_type(v_fst_2776_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
v___x_2789_ = lean_whnf(v_a_2788_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = l_Lean_Expr_isForall(v_a_2790_);
lean_dec(v_a_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_del_object(v___x_2774_);
lean_del_object(v___x_2766_);
v___x_2792_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2793_ = l_Lean_indentExpr(v_expr_2732_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 7);
lean_ctor_set(v___x_2778_, 1, v___x_2793_);
lean_ctor_set(v___x_2778_, 0, v___x_2792_);
v___x_2795_ = v___x_2778_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v___x_2796_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_indentExpr(v_fst_2776_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2801_ = l_Lean_indentExpr(v_a_2764_);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = l_Lean_MessageData_hint_x27(v___x_2802_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2799_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2804_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_del_object(v___x_2778_);
lean_dec(v_a_2764_);
lean_dec_ref(v_expr_2732_);
goto v___jp_2780_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2778_);
lean_dec(v_fst_2776_);
lean_del_object(v___x_2774_);
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_dec_ref(v_expr_2732_);
v_a_2815_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2789_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2789_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
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
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2778_);
lean_dec(v_fst_2776_);
lean_del_object(v___x_2774_);
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_dec_ref(v_expr_2732_);
v_a_2823_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2787_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2787_);
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
v___jp_2780_:
{
lean_object* v___x_2782_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_fst_2776_);
v___x_2782_ = v___x_2766_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_fst_2776_);
v___x_2782_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2784_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2782_);
v___x_2784_ = v___x_2774_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_del_object(v___x_2766_);
lean_dec(v_a_2764_);
lean_dec_ref(v_expr_2732_);
v_a_2834_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2771_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2771_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v___x_2844_; 
lean_dec(v_a_2760_);
lean_dec_ref_known(v___x_2755_, 2);
lean_dec(v_a_2751_);
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2758_);
v___x_2844_ = v___x_2762_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2758_);
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
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref_known(v___x_2755_, 2);
lean_dec(v_a_2751_);
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
v_a_2847_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2759_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2759_);
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
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2743_);
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
v_a_2855_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2750_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2750_);
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
lean_dec(v_a_2743_);
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
v_a_2863_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2745_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2745_);
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
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
v_a_2871_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2742_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2742_);
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
lean_dec(v_a_2739_);
lean_dec_ref(v_expr_2732_);
v_a_2879_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2740_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2740_);
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
lean_dec_ref(v_expr_2732_);
v_a_2887_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2738_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2738_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2901_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2910_ = l_Lean_stringToMessageData(v___x_2909_);
return v___x_2910_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2913_ = l_Lean_stringToMessageData(v___x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2920_; 
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
lean_inc_ref(v_expr_2914_);
v___x_2920_ = lean_infer_type(v_expr_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_n(v_a_2921_, 2);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = l_Lean_Meta_getLevel(v_a_2921_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc_n(v_a_2925_, 2);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_mkSort(v_a_2925_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = 0;
v___x_2929_ = lean_box(0);
v___x_2930_ = l_Lean_Meta_mkFreshExprMVar(v___x_2927_, v___x_2928_, v___x_2929_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_n(v_a_2931_, 2);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2934_, 0, v_a_2925_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2935_, 0, v_a_2923_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
lean_inc_ref(v___x_2935_);
v___x_2936_ = l_Lean_Expr_const___override(v___x_2932_, v___x_2935_);
lean_inc(v_a_2921_);
v___x_2937_ = l_Lean_mkAppB(v___x_2936_, v_a_2921_, v_a_2931_);
v___x_2938_ = lean_box(0);
v___x_2939_ = l_Lean_Meta_trySynthInstance(v___x_2937_, v___x_2938_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3026_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_3026_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3026_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
if (lean_obj_tag(v_a_2940_) == 1)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3022_; 
lean_del_object(v___x_2942_);
v_a_2944_ = lean_ctor_get(v_a_2940_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2946_ = v_a_2940_;
v_isShared_2947_ = v_isSharedCheck_3022_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v_a_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3022_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2948_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2949_ = l_Lean_Expr_const___override(v___x_2948_, v___x_2935_);
lean_inc_ref(v_expr_2914_);
lean_inc(v_a_2944_);
v___x_2950_ = l_Lean_mkApp4(v___x_2949_, v_a_2921_, v_a_2931_, v_a_2944_, v_expr_2914_);
v___x_2951_ = l_Lean_Meta_expandCoe(v___x_2950_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3013_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_3013_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3013_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_fst_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3011_; 
v_fst_2956_ = lean_ctor_get(v_a_2952_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_a_2952_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v_a_2952_, 1);
lean_dec(v_unused_3012_);
v___x_2958_ = v_a_2952_;
v_isShared_2959_ = v_isSharedCheck_3011_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_fst_2956_);
lean_dec(v_a_2952_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3011_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2967_; 
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
lean_inc(v_fst_2956_);
v___x_2967_ = lean_infer_type(v_fst_2956_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
lean_inc(v_a_2918_);
lean_inc_ref(v_a_2917_);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
v___x_2969_ = lean_whnf(v_a_2968_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; uint8_t v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l_Lean_Expr_isSort(v_a_2970_);
lean_dec(v_a_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_del_object(v___x_2954_);
lean_del_object(v___x_2946_);
v___x_2972_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2973_ = l_Lean_indentExpr(v_expr_2914_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 7);
lean_ctor_set(v___x_2958_, 1, v___x_2973_);
lean_ctor_set(v___x_2958_, 0, v___x_2972_);
v___x_2975_ = v___x_2958_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v___x_2976_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = l_Lean_indentExpr(v_fst_2956_);
v___x_2979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_2981_ = l_Lean_indentExpr(v_a_2944_);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_MessageData_hint_x27(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2979_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2984_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_del_object(v___x_2958_);
lean_dec(v_a_2944_);
lean_dec_ref(v_expr_2914_);
goto v___jp_2960_;
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2946_);
lean_dec(v_a_2944_);
lean_dec_ref(v_expr_2914_);
v_a_2995_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2969_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2969_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
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
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2958_);
lean_dec(v_fst_2956_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2946_);
lean_dec(v_a_2944_);
lean_dec_ref(v_expr_2914_);
v_a_3003_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2967_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2967_);
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
v___jp_2960_:
{
lean_object* v___x_2962_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v_fst_2956_);
v___x_2962_ = v___x_2946_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_fst_2956_);
v___x_2962_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2962_);
v___x_2964_ = v___x_2954_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_del_object(v___x_2946_);
lean_dec(v_a_2944_);
lean_dec_ref(v_expr_2914_);
v_a_3014_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2951_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2951_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
else
{
lean_object* v___x_3024_; 
lean_dec(v_a_2940_);
lean_dec_ref_known(v___x_2935_, 2);
lean_dec(v_a_2931_);
lean_dec(v_a_2921_);
lean_dec_ref(v_expr_2914_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2938_);
v___x_3024_ = v___x_2942_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_2938_);
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
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref_known(v___x_2935_, 2);
lean_dec(v_a_2931_);
lean_dec(v_a_2921_);
lean_dec_ref(v_expr_2914_);
v_a_3027_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2939_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2939_);
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
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2923_);
lean_dec(v_a_2921_);
lean_dec_ref(v_expr_2914_);
v_a_3035_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2930_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2930_);
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
lean_dec(v_a_2923_);
lean_dec(v_a_2921_);
lean_dec_ref(v_expr_2914_);
v_a_3043_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2924_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2924_);
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
lean_dec(v_a_2921_);
lean_dec_ref(v_expr_2914_);
v_a_3051_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_2922_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_2922_);
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
lean_dec_ref(v_expr_2914_);
v_a_3059_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2920_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_2920_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = l_Lean_Expr_hasMVar(v_e_3074_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_e_3074_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v_mctx_3080_; lean_object* v___x_3081_; lean_object* v_fst_3082_; lean_object* v_snd_3083_; lean_object* v___x_3084_; lean_object* v_cache_3085_; lean_object* v_zetaDeltaFVarIds_3086_; lean_object* v_postponed_3087_; lean_object* v_diag_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3097_; 
v___x_3079_ = lean_st_ref_get(v___y_3075_);
v_mctx_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc_ref(v_mctx_3080_);
lean_dec(v___x_3079_);
v___x_3081_ = l_Lean_instantiateMVarsCore(v_mctx_3080_, v_e_3074_);
v_fst_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_fst_3082_);
v_snd_3083_ = lean_ctor_get(v___x_3081_, 1);
lean_inc(v_snd_3083_);
lean_dec_ref(v___x_3081_);
v___x_3084_ = lean_st_ref_take(v___y_3075_);
v_cache_3085_ = lean_ctor_get(v___x_3084_, 1);
v_zetaDeltaFVarIds_3086_ = lean_ctor_get(v___x_3084_, 2);
v_postponed_3087_ = lean_ctor_get(v___x_3084_, 3);
v_diag_3088_ = lean_ctor_get(v___x_3084_, 4);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3084_, 0);
lean_dec(v_unused_3098_);
v___x_3090_ = v___x_3084_;
v_isShared_3091_ = v_isSharedCheck_3097_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_diag_3088_);
lean_inc(v_postponed_3087_);
lean_inc(v_zetaDeltaFVarIds_3086_);
lean_inc(v_cache_3085_);
lean_dec(v___x_3084_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3097_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_snd_3083_);
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_snd_3083_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_cache_3085_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_zetaDeltaFVarIds_3086_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_postponed_3087_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_diag_3088_);
v___x_3093_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_st_ref_set(v___y_3075_, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_fst_3082_);
return v___x_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3099_, v___y_3100_);
lean_dec(v___y_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3103_, v___y_3105_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_keyedConfig_3123_; uint8_t v_trackZetaDelta_3124_; lean_object* v_zetaDeltaSet_3125_; lean_object* v_lctx_3126_; lean_object* v_localInstances_3127_; lean_object* v_defEqCtx_x3f_3128_; lean_object* v_synthPendingDepth_3129_; lean_object* v_customCanUnfoldPredicate_x3f_3130_; uint8_t v_univApprox_3131_; uint8_t v_inTypeClassResolution_3132_; uint8_t v_cacheInferType_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_keyedConfig_3123_ = lean_ctor_get(v_a_3118_, 0);
v_trackZetaDelta_3124_ = lean_ctor_get_uint8(v_a_3118_, sizeof(void*)*7);
v_zetaDeltaSet_3125_ = lean_ctor_get(v_a_3118_, 1);
v_lctx_3126_ = lean_ctor_get(v_a_3118_, 2);
v_localInstances_3127_ = lean_ctor_get(v_a_3118_, 3);
v_defEqCtx_x3f_3128_ = lean_ctor_get(v_a_3118_, 4);
v_synthPendingDepth_3129_ = lean_ctor_get(v_a_3118_, 5);
v_customCanUnfoldPredicate_x3f_3130_ = lean_ctor_get(v_a_3118_, 6);
v_univApprox_3131_ = lean_ctor_get_uint8(v_a_3118_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3132_ = lean_ctor_get_uint8(v_a_3118_, sizeof(void*)*7 + 2);
v_cacheInferType_3133_ = lean_ctor_get_uint8(v_a_3118_, sizeof(void*)*7 + 3);
v___x_3134_ = 2;
lean_inc_ref(v_keyedConfig_3123_);
v___x_3135_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3134_, v_keyedConfig_3123_);
lean_inc(v_customCanUnfoldPredicate_x3f_3130_);
lean_inc(v_synthPendingDepth_3129_);
lean_inc(v_defEqCtx_x3f_3128_);
lean_inc_ref(v_localInstances_3127_);
lean_inc_ref(v_lctx_3126_);
lean_inc(v_zetaDeltaSet_3125_);
v___x_3136_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v_zetaDeltaSet_3125_);
lean_ctor_set(v___x_3136_, 2, v_lctx_3126_);
lean_ctor_set(v___x_3136_, 3, v_localInstances_3127_);
lean_ctor_set(v___x_3136_, 4, v_defEqCtx_x3f_3128_);
lean_ctor_set(v___x_3136_, 5, v_synthPendingDepth_3129_);
lean_ctor_set(v___x_3136_, 6, v_customCanUnfoldPredicate_x3f_3130_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7, v_trackZetaDelta_3124_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 1, v_univApprox_3131_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3132_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*7 + 3, v_cacheInferType_3133_);
lean_inc(v_a_3121_);
lean_inc_ref(v_a_3120_);
lean_inc(v_a_3119_);
v___x_3137_ = lean_whnf(v_type_3117_, v___x_3136_, v_a_3119_, v_a_3120_, v_a_3121_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3167_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3167_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
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
v___x_3144_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3142_, v_a_3119_);
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
v___x_3149_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3143_, v_a_3119_);
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
v_a_3168_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3137_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3137_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_Meta_isTypeApp_x3f(v_type_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_isTypeApp_x3f(v_type_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3225_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3225_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3225_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
if (lean_obj_tag(v_a_3190_) == 1)
{
lean_object* v_val_3194_; lean_object* v_fst_3195_; lean_object* v___x_3196_; 
lean_del_object(v___x_3192_);
v_val_3194_ = lean_ctor_get(v_a_3190_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v_a_3190_, 1);
v_fst_3195_ = lean_ctor_get(v_val_3194_, 0);
lean_inc(v_fst_3195_);
lean_dec(v_val_3194_);
v___x_3196_ = l_Lean_Meta_isMonad_x3f(v_fst_3195_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3211_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
if (lean_obj_tag(v_a_3197_) == 0)
{
uint8_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3201_ = 0;
v___x_3202_ = lean_box(v___x_3201_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3202_);
v___x_3204_ = v___x_3199_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
else
{
uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_dec_ref_known(v_a_3197_, 1);
v___x_3206_ = 1;
v___x_3207_ = lean_box(v___x_3206_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3207_);
v___x_3209_ = v___x_3199_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
v_a_3212_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3196_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3196_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec(v_a_3190_);
v___x_3220_ = 0;
v___x_3221_ = lean_box(v___x_3220_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3221_);
v___x_3223_ = v___x_3192_;
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
v_a_3226_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3189_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3189_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Meta_isMonadApp(v_type_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
return v_res_3240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3241_, lean_object* v_opt_3242_){
_start:
{
lean_object* v_name_3243_; lean_object* v_defValue_3244_; lean_object* v_map_3245_; lean_object* v___x_3246_; 
v_name_3243_ = lean_ctor_get(v_opt_3242_, 0);
v_defValue_3244_ = lean_ctor_get(v_opt_3242_, 1);
v_map_3245_ = lean_ctor_get(v_opts_3241_, 0);
v___x_3246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3245_, v_name_3243_);
if (lean_obj_tag(v___x_3246_) == 0)
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_unbox(v_defValue_3244_);
return v___x_3247_;
}
else
{
lean_object* v_val_3248_; 
v_val_3248_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_val_3248_);
lean_dec_ref_known(v___x_3246_, 1);
if (lean_obj_tag(v_val_3248_) == 1)
{
uint8_t v_v_3249_; 
v_v_3249_ = lean_ctor_get_uint8(v_val_3248_, 0);
lean_dec_ref_known(v_val_3248_, 0);
return v_v_3249_;
}
else
{
uint8_t v___x_3250_; 
lean_dec(v_val_3248_);
v___x_3250_ = lean_unbox(v_defValue_3244_);
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3251_, lean_object* v_opt_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3251_, v_opt_3252_);
lean_dec_ref(v_opt_3252_);
lean_dec_ref(v_opts_3251_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v_x_3265_);
return v_res_3271_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = l_Lean_mkBVar(v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3294_, lean_object* v_expectedType_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v___y_3302_; uint8_t v___y_3303_; lean_object* v_a_3308_; lean_object* v___y_3312_; lean_object* v___x_3322_; lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3726_; 
v___x_3322_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3295_, v_a_3297_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3726_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3726_;
goto v_resetjp_3324_;
}
v___jp_3301_:
{
if (v___y_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v___y_3302_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___y_3302_);
return v___x_3306_;
}
}
v___jp_3307_:
{
uint8_t v___x_3309_; 
v___x_3309_ = l_Lean_Exception_isInterrupt(v_a_3308_);
if (v___x_3309_ == 0)
{
uint8_t v___x_3310_; 
lean_inc_ref(v_a_3308_);
v___x_3310_ = l_Lean_Exception_isRuntime(v_a_3308_);
v___y_3302_ = v_a_3308_;
v___y_3303_ = v___x_3310_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v_a_3308_;
v___y_3303_ = v___x_3309_;
goto v___jp_3301_;
}
}
v___jp_3311_:
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3321_; 
v_a_3313_ = lean_ctor_get(v___y_3312_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___y_3312_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3315_ = v___y_3312_;
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___y_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v_a_3317_; lean_object* v___x_3319_; 
v_a_3317_ = lean_ctor_get(v_a_3313_, 0);
lean_inc(v_a_3317_);
lean_dec(v_a_3313_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v_a_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; 
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
lean_inc_ref(v_e_3294_);
v___x_3327_ = lean_infer_type(v_e_3294_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3717_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3328_, v_a_3297_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3717_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3717_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; 
lean_inc(v_a_3323_);
v___x_3334_ = l_Lean_Meta_isTypeApp_x3f(v_a_3323_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3708_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3708_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3708_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
if (lean_obj_tag(v_a_3335_) == 1)
{
lean_object* v_val_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3703_; 
lean_del_object(v___x_3337_);
v_val_3339_ = lean_ctor_get(v_a_3335_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_a_3335_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3341_ = v_a_3335_;
v_isShared_3342_ = v_isSharedCheck_3703_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_val_3339_);
lean_dec(v_a_3335_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3703_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3702_; 
v_fst_3343_ = lean_ctor_get(v_val_3339_, 0);
v_snd_3344_ = lean_ctor_get(v_val_3339_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_val_3339_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3346_ = v_val_3339_;
v_isShared_3347_ = v_isSharedCheck_3702_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_snd_3344_);
lean_inc(v_fst_3343_);
lean_dec(v_val_3339_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3702_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; 
lean_inc(v_a_3330_);
v___x_3348_ = l_Lean_Meta_isTypeApp_x3f(v_a_3330_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3693_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3693_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3693_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 1)
{
lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3351_);
v_val_3353_ = lean_ctor_get(v_a_3349_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_a_3349_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3355_ = v_a_3349_;
v_isShared_3356_ = v_isSharedCheck_3688_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v_a_3349_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3688_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3687_; 
v_fst_3357_ = lean_ctor_get(v_val_3353_, 0);
v_snd_3358_ = lean_ctor_get(v_val_3353_, 1);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_val_3353_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3360_ = v_val_3353_;
v_isShared_3361_ = v_isSharedCheck_3687_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_val_3353_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3687_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_Meta_saveState___redArg(v_a_3297_, v_a_3299_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
lean_inc(v_fst_3343_);
lean_inc(v_fst_3357_);
v___x_3364_ = l_Lean_Meta_isExprDefEq(v_fst_3357_, v_fst_3343_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3670_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3670_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3670_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_unbox(v_a_3365_);
lean_dec(v_a_3365_);
if (v___x_3369_ == 0)
{
lean_object* v_options_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
lean_dec(v_a_3363_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_del_object(v___x_3325_);
v_options_3370_ = lean_ctor_get(v_a_3298_, 2);
v___x_3371_ = l_Lean_Meta_autoLift;
v___x_3372_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3373_ = lean_box(0);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3373_);
v___x_3375_ = v___x_3367_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
else
{
lean_object* v___x_3377_; 
lean_del_object(v___x_3367_);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
lean_inc(v_fst_3357_);
v___x_3377_ = lean_infer_type(v_fst_3357_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
v___x_3379_ = lean_whnf(v_a_3378_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
if (lean_obj_tag(v_a_3380_) == 7)
{
lean_object* v_binderType_3381_; 
v_binderType_3381_ = lean_ctor_get(v_a_3380_, 1);
if (lean_obj_tag(v_binderType_3381_) == 3)
{
lean_object* v_body_3382_; 
v_body_3382_ = lean_ctor_get(v_a_3380_, 2);
if (lean_obj_tag(v_body_3382_) == 3)
{
lean_object* v_u_3383_; lean_object* v_u_3384_; lean_object* v___x_3385_; 
lean_inc_ref(v_body_3382_);
lean_inc_ref(v_binderType_3381_);
lean_dec_ref_known(v_a_3380_, 3);
v_u_3383_ = lean_ctor_get(v_binderType_3381_, 0);
lean_inc(v_u_3383_);
lean_dec_ref_known(v_binderType_3381_, 1);
v_u_3384_ = lean_ctor_get(v_body_3382_, 0);
lean_inc(v_u_3384_);
lean_dec_ref_known(v_body_3382_, 1);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
lean_inc(v_fst_3343_);
v___x_3385_ = lean_infer_type(v_fst_3343_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
v___x_3387_ = lean_whnf(v_a_3386_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
if (lean_obj_tag(v_a_3388_) == 7)
{
lean_object* v_binderType_3389_; 
v_binderType_3389_ = lean_ctor_get(v_a_3388_, 1);
if (lean_obj_tag(v_binderType_3389_) == 3)
{
lean_object* v_body_3390_; 
v_body_3390_ = lean_ctor_get(v_a_3388_, 2);
if (lean_obj_tag(v_body_3390_) == 3)
{
lean_object* v_u_3391_; lean_object* v_u_3392_; lean_object* v___x_3393_; 
lean_inc_ref(v_body_3390_);
lean_inc_ref(v_binderType_3389_);
lean_dec_ref_known(v_a_3388_, 3);
v_u_3391_ = lean_ctor_get(v_binderType_3389_, 0);
lean_inc(v_u_3391_);
lean_dec_ref_known(v_binderType_3389_, 1);
v_u_3392_ = lean_ctor_get(v_body_3390_, 0);
lean_inc(v_u_3392_);
lean_dec_ref_known(v_body_3390_, 1);
v___x_3393_ = l_Lean_Meta_decLevel(v_u_3383_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = l_Lean_Meta_decLevel(v_u_3391_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
lean_inc(v_a_3394_);
v___x_3397_ = l_Lean_Meta_isLevelDefEq(v_a_3394_, v_a_3396_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3562_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3562_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3562_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_unbox(v_a_3398_);
lean_dec(v_a_3398_);
if (v___x_3402_ == 1)
{
lean_object* v___x_3403_; 
lean_del_object(v___x_3400_);
v___x_3403_ = l_Lean_Meta_decLevel(v_u_3384_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = l_Lean_Meta_decLevel(v_u_3392_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3408_ = lean_box(0);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
lean_ctor_set(v___x_3360_, 1, v___x_3408_);
lean_ctor_set(v___x_3360_, 0, v_a_3406_);
v___x_3410_ = v___x_3360_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3406_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3412_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 1);
lean_ctor_set(v___x_3346_, 1, v___x_3410_);
lean_ctor_set(v___x_3346_, 0, v_a_3404_);
v___x_3412_ = v___x_3346_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3404_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v_a_3394_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = l_Lean_Expr_const___override(v___x_3407_, v___x_3413_);
v___x_3415_ = lean_unsigned_to_nat(2u);
v___x_3416_ = lean_mk_empty_array_with_capacity(v___x_3415_);
lean_inc(v_fst_3357_);
v___x_3417_ = lean_array_push(v___x_3416_, v_fst_3357_);
lean_inc(v_fst_3343_);
v___x_3418_ = lean_array_push(v___x_3417_, v_fst_3343_);
v___x_3419_ = l_Lean_mkAppN(v___x_3414_, v___x_3418_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = lean_box(0);
v___x_3421_ = l_Lean_Meta_trySynthInstance(v___x_3419_, v___x_3420_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3552_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3552_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3552_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
if (lean_obj_tag(v_a_3422_) == 1)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
lean_del_object(v___x_3424_);
v_a_3426_ = lean_ctor_get(v_a_3422_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v_a_3422_, 1);
lean_inc(v_snd_3358_);
v___x_3427_ = l_Lean_Meta_getDecLevel(v_snd_3358_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = l_Lean_Meta_getDecLevel(v_a_3330_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
lean_inc(v_a_3323_);
v___x_3431_ = l_Lean_Meta_getDecLevel(v_a_3323_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v_a_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3408_);
v___x_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_a_3430_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_a_3428_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
lean_inc_ref(v___x_3436_);
v___x_3437_ = l_Lean_mkConst(v___x_3433_, v___x_3436_);
v___x_3438_ = lean_unsigned_to_nat(5u);
v___x_3439_ = lean_mk_empty_array_with_capacity(v___x_3438_);
lean_inc(v_fst_3357_);
v___x_3440_ = lean_array_push(v___x_3439_, v_fst_3357_);
lean_inc(v_fst_3343_);
v___x_3441_ = lean_array_push(v___x_3440_, v_fst_3343_);
lean_inc(v_a_3426_);
v___x_3442_ = lean_array_push(v___x_3441_, v_a_3426_);
lean_inc(v_snd_3358_);
v___x_3443_ = lean_array_push(v___x_3442_, v_snd_3358_);
lean_inc_ref(v_e_3294_);
v___x_3444_ = lean_array_push(v___x_3443_, v_e_3294_);
v___x_3445_ = l_Lean_mkAppN(v___x_3437_, v___x_3444_);
lean_dec_ref(v___x_3444_);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = lean_infer_type(v___x_3445_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
lean_inc(v_a_3323_);
v___x_3448_ = l_Lean_Meta_isExprDefEq(v_a_3323_, v_a_3447_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3543_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3543_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3543_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_unbox(v_a_3449_);
lean_dec(v_a_3449_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
lean_del_object(v___x_3451_);
lean_dec_ref(v___x_3445_);
lean_del_object(v___x_3355_);
lean_inc(v_fst_3343_);
v___x_3454_ = l_Lean_Meta_isMonad_x3f(v_fst_3343_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3535_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3535_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3535_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
if (lean_obj_tag(v_a_3455_) == 1)
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3457_);
v_val_3459_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3461_ = v_a_3455_;
v_isShared_3462_ = v_isSharedCheck_3531_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v_a_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3531_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; 
lean_inc(v_snd_3358_);
v___x_3463_ = l_Lean_Meta_getLevel(v_snd_3358_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
lean_inc(v_snd_3344_);
v___x_3465_ = l_Lean_Meta_getLevel(v_snd_3344_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3468_ = 0;
v___x_3469_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_a_3466_);
lean_ctor_set(v___x_3470_, 1, v___x_3408_);
v___x_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3471_, 0, v_a_3464_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l_Lean_mkConst(v___x_3469_, v___x_3471_);
v___x_3473_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3474_ = lean_unsigned_to_nat(3u);
v___x_3475_ = lean_mk_empty_array_with_capacity(v___x_3474_);
lean_inc_n(v_snd_3358_, 2);
v___x_3476_ = lean_array_push(v___x_3475_, v_snd_3358_);
v___x_3477_ = lean_array_push(v___x_3476_, v___x_3473_);
lean_inc(v_snd_3344_);
v___x_3478_ = lean_array_push(v___x_3477_, v_snd_3344_);
v___x_3479_ = l_Lean_mkAppN(v___x_3472_, v___x_3478_);
lean_dec_ref(v___x_3478_);
v___x_3480_ = l_Lean_mkForall(v___x_3467_, v___x_3468_, v_snd_3358_, v___x_3479_);
v___x_3481_ = l_Lean_Meta_trySynthInstance(v___x_3480_, v___x_3420_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3527_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3527_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3527_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
if (lean_obj_tag(v_a_3482_) == 1)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_del_object(v___x_3484_);
v_a_3486_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v_a_3482_, 1);
v___x_3487_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3488_ = l_Lean_mkConst(v___x_3487_, v___x_3436_);
v___x_3489_ = lean_unsigned_to_nat(8u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
v___x_3491_ = lean_array_push(v___x_3490_, v_fst_3357_);
v___x_3492_ = lean_array_push(v___x_3491_, v_fst_3343_);
v___x_3493_ = lean_array_push(v___x_3492_, v_snd_3358_);
v___x_3494_ = lean_array_push(v___x_3493_, v_snd_3344_);
v___x_3495_ = lean_array_push(v___x_3494_, v_a_3426_);
v___x_3496_ = lean_array_push(v___x_3495_, v_a_3486_);
v___x_3497_ = lean_array_push(v___x_3496_, v_val_3459_);
v___x_3498_ = lean_array_push(v___x_3497_, v_e_3294_);
v___x_3499_ = l_Lean_mkAppN(v___x_3488_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3500_ = l_Lean_Meta_expandCoe(v___x_3499_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_fst_3502_; lean_object* v___x_3503_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v_fst_3502_ = lean_ctor_get(v_a_3501_, 0);
lean_inc_n(v_fst_3502_, 2);
lean_dec(v_a_3501_);
lean_inc(v_a_3299_);
lean_inc_ref(v_a_3298_);
lean_inc(v_a_3297_);
lean_inc_ref(v_a_3296_);
v___x_3503_ = lean_infer_type(v_fst_3502_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_Meta_isExprDefEq(v_a_3323_, v_a_3504_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3520_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3520_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3520_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_unbox(v_a_3506_);
lean_dec(v_a_3506_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v_fst_3502_);
lean_del_object(v___x_3461_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3420_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3420_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
else
{
lean_object* v___x_3515_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v_fst_3502_);
v___x_3515_ = v___x_3461_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_fst_3502_);
v___x_3515_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3515_);
v___x_3517_ = v___x_3508_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
else
{
lean_object* v_a_3521_; 
lean_dec(v_fst_3502_);
lean_del_object(v___x_3461_);
v_a_3521_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3505_, 1);
v_a_3308_ = v_a_3521_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3522_; 
lean_dec(v_fst_3502_);
lean_del_object(v___x_3461_);
lean_dec(v_a_3323_);
v_a_3522_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3503_, 1);
v_a_3308_ = v_a_3522_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3523_; 
lean_del_object(v___x_3461_);
lean_dec(v_a_3323_);
v_a_3523_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3500_, 1);
v_a_3308_ = v_a_3523_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3525_; 
lean_dec(v_a_3482_);
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3420_);
v___x_3525_ = v___x_3484_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3420_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3528_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3481_, 1);
v_a_3308_ = v_a_3528_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3529_; 
lean_dec(v_a_3464_);
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3529_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3465_, 1);
v_a_3308_ = v_a_3529_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3530_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3530_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3463_, 1);
v_a_3308_ = v_a_3530_;
goto v___jp_3307_;
}
}
}
else
{
lean_object* v___x_3533_; 
lean_dec(v_a_3455_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3420_);
v___x_3533_ = v___x_3457_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3420_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; 
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3536_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3454_, 1);
v_a_3308_ = v_a_3536_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3445_);
v___x_3538_ = v___x_3355_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3445_);
v___x_3538_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3540_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3538_);
v___x_3540_ = v___x_3451_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3544_; 
lean_dec_ref(v___x_3445_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3544_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3448_, 1);
v_a_3308_ = v_a_3544_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3545_; 
lean_dec_ref(v___x_3445_);
lean_dec_ref_known(v___x_3436_, 2);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3545_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3446_, 1);
v_a_3308_ = v_a_3545_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3546_; 
lean_dec(v_a_3430_);
lean_dec(v_a_3428_);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3546_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3431_, 1);
v_a_3308_ = v_a_3546_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3547_; 
lean_dec(v_a_3428_);
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3547_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3429_, 1);
v_a_3308_ = v_a_3547_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3548_; 
lean_dec(v_a_3426_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3548_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3427_, 1);
v_a_3308_ = v_a_3548_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3550_; 
lean_dec(v_a_3422_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3420_);
v___x_3550_ = v___x_3424_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3420_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; 
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3553_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3421_, 1);
v_a_3308_ = v_a_3553_;
goto v___jp_3307_;
}
}
}
}
else
{
lean_object* v_a_3556_; 
lean_dec(v_a_3404_);
lean_dec(v_a_3394_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3556_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3405_, 1);
v_a_3308_ = v_a_3556_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3557_; 
lean_dec(v_a_3394_);
lean_dec(v_u_3392_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3557_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3403_, 1);
v_a_3308_ = v_a_3557_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
lean_dec(v_a_3394_);
lean_dec(v_u_3392_);
lean_dec(v_u_3384_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3558_ = lean_box(0);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v___x_3558_);
v___x_3560_ = v___x_3400_;
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
else
{
lean_object* v_a_3563_; 
lean_dec(v_a_3394_);
lean_dec(v_u_3392_);
lean_dec(v_u_3384_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3563_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3397_, 1);
v_a_3308_ = v_a_3563_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3564_; 
lean_dec(v_a_3394_);
lean_dec(v_u_3392_);
lean_dec(v_u_3384_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3564_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3395_, 1);
v_a_3308_ = v_a_3564_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3565_; 
lean_dec(v_u_3392_);
lean_dec(v_u_3391_);
lean_dec(v_u_3384_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3565_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3393_, 1);
v_a_3308_ = v_a_3565_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3566_; 
lean_dec(v_u_3384_);
lean_dec(v_u_3383_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3566_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3388_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec_ref_known(v_a_3388_, 3);
v___y_3312_ = v___x_3566_;
goto v___jp_3311_;
}
}
else
{
lean_object* v___x_3567_; 
lean_dec(v_u_3384_);
lean_dec(v_u_3383_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3567_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3388_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec_ref_known(v_a_3388_, 3);
v___y_3312_ = v___x_3567_;
goto v___jp_3311_;
}
}
else
{
lean_object* v___x_3568_; 
lean_dec(v_u_3384_);
lean_dec(v_u_3383_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3568_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3388_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3388_);
v___y_3312_ = v___x_3568_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3569_; 
lean_dec(v_u_3384_);
lean_dec(v_u_3383_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3569_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3387_, 1);
v_a_3308_ = v_a_3569_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3570_; 
lean_dec(v_u_3384_);
lean_dec(v_u_3383_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3570_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3385_, 1);
v_a_3308_ = v_a_3570_;
goto v___jp_3307_;
}
}
else
{
lean_object* v___x_3571_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3571_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3380_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec_ref_known(v_a_3380_, 3);
v___y_3312_ = v___x_3571_;
goto v___jp_3311_;
}
}
else
{
lean_object* v___x_3572_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3572_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3380_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec_ref_known(v_a_3380_, 3);
v___y_3312_ = v___x_3572_;
goto v___jp_3311_;
}
}
else
{
lean_object* v___x_3573_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3573_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3380_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3380_);
v___y_3312_ = v___x_3573_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3574_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3574_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3379_, 1);
v_a_3308_ = v_a_3574_;
goto v___jp_3307_;
}
}
else
{
lean_object* v_a_3575_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3575_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3377_, 1);
v_a_3308_ = v_a_3575_;
goto v___jp_3307_;
}
}
}
else
{
lean_object* v___x_3576_; 
lean_del_object(v___x_3367_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3346_);
lean_dec(v_a_3330_);
lean_dec(v_a_3323_);
v___x_3576_ = l_Lean_Meta_isMonad_x3f(v_fst_3343_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3669_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3669_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3669_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
if (lean_obj_tag(v_a_3577_) == 1)
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v_fst_3357_);
v___x_3583_ = v___x_3355_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_fst_3357_);
v___x_3583_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_snd_3358_);
v___x_3585_ = v___x_3341_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_snd_3358_);
v___x_3585_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 1);
lean_ctor_set(v___x_3332_, 0, v_snd_3344_);
v___x_3587_ = v___x_3332_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_snd_3344_);
v___x_3587_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v_a_3613_; lean_object* v___x_3617_; 
v___x_3588_ = lean_box(0);
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 1);
lean_ctor_set(v___x_3325_, 0, v_e_3294_);
v___x_3617_ = v___x_3325_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_e_3294_);
v___x_3617_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3616_;
}
v___jp_3589_:
{
if (v___y_3591_ == 0)
{
lean_object* v___x_3592_; 
lean_dec_ref(v___y_3590_);
lean_del_object(v___x_3579_);
v___x_3592_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3363_, v_a_3297_, v_a_3299_);
lean_dec(v_a_3363_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; 
v_unused_3600_ = lean_ctor_get(v___x_3592_, 0);
lean_dec(v_unused_3600_);
v___x_3594_ = v___x_3592_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_dec(v___x_3592_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3588_);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3588_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_a_3601_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3592_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3592_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_a_3363_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set_tag(v___x_3579_, 1);
lean_ctor_set(v___x_3579_, 0, v___y_3590_);
v___x_3610_ = v___x_3579_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___y_3590_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
v___jp_3612_:
{
uint8_t v___x_3614_; 
v___x_3614_ = l_Lean_Exception_isInterrupt(v_a_3613_);
if (v___x_3614_ == 0)
{
uint8_t v___x_3615_; 
lean_inc_ref(v_a_3613_);
v___x_3615_ = l_Lean_Exception_isRuntime(v_a_3613_);
v___y_3590_ = v_a_3613_;
v___y_3591_ = v___x_3615_;
goto v___jp_3589_;
}
else
{
v___y_3590_ = v_a_3613_;
v___y_3591_ = v___x_3614_;
goto v___jp_3589_;
}
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3618_ = lean_unsigned_to_nat(6u);
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_3618_);
v___x_3620_ = lean_array_push(v___x_3619_, v___x_3583_);
v___x_3621_ = lean_array_push(v___x_3620_, v___x_3585_);
v___x_3622_ = lean_array_push(v___x_3621_, v___x_3587_);
v___x_3623_ = lean_array_push(v___x_3622_, v___x_3588_);
v___x_3624_ = lean_array_push(v___x_3623_, v_a_3577_);
v___x_3625_ = lean_array_push(v___x_3624_, v___x_3617_);
v___x_3626_ = l_Lean_Meta_mkAppOptM(v___x_3581_, v___x_3625_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3645_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3645_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3645_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_Meta_expandCoe(v_a_3627_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3643_; 
lean_del_object(v___x_3579_);
lean_dec(v_a_3363_);
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3643_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3643_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_fst_3636_; lean_object* v___x_3638_; 
v_fst_3636_ = lean_ctor_get(v_a_3632_, 0);
lean_inc(v_fst_3636_);
lean_dec(v_a_3632_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set_tag(v___x_3629_, 1);
lean_ctor_set(v___x_3629_, 0, v_fst_3636_);
v___x_3638_ = v___x_3629_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_fst_3636_);
v___x_3638_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3638_);
v___x_3640_ = v___x_3634_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
else
{
lean_object* v_a_3644_; 
lean_del_object(v___x_3629_);
v_a_3644_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3631_, 1);
v_a_3613_ = v_a_3644_;
goto v___jp_3612_;
}
}
}
else
{
lean_object* v_a_3646_; 
v_a_3646_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3626_, 1);
v_a_3613_ = v_a_3646_;
goto v___jp_3612_;
}
}
}
}
}
}
else
{
lean_object* v___x_3651_; 
lean_del_object(v___x_3579_);
lean_dec(v_a_3577_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_del_object(v___x_3325_);
lean_dec_ref(v_e_3294_);
v___x_3651_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3363_, v_a_3297_, v_a_3299_);
lean_dec(v_a_3363_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3659_; 
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3651_, 0);
lean_dec(v_unused_3660_);
v___x_3653_ = v___x_3651_;
v_isShared_3654_ = v_isSharedCheck_3659_;
goto v_resetjp_3652_;
}
else
{
lean_dec(v___x_3651_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3659_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3655_ = lean_box(0);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3655_);
v___x_3657_ = v___x_3653_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
v_a_3661_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3651_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3651_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3363_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec(v_snd_3344_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_del_object(v___x_3325_);
lean_dec_ref(v_e_3294_);
return v___x_3576_;
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v_a_3363_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3671_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3364_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3364_);
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
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3679_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3362_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3362_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_dec(v_a_3349_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3689_ = lean_box(0);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3689_);
v___x_3691_ = v___x_3351_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec(v_fst_3343_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3694_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3348_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3348_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec(v_a_3335_);
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v___x_3704_ = lean_box(0);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3704_);
v___x_3706_ = v___x_3337_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3332_);
lean_dec(v_a_3330_);
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3709_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3334_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3334_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
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
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3325_);
lean_dec(v_a_3323_);
lean_dec_ref(v_e_3294_);
v_a_3718_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3327_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3327_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3727_, lean_object* v_expectedType_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3727_, v_expectedType_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3735_, lean_object* v_expectedType_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v___x_3742_; 
lean_inc_ref(v_expectedType_3736_);
lean_inc_ref(v_expr_3735_);
v___x_3742_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3735_, v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3822_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3822_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3822_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
if (lean_obj_tag(v_a_3743_) == 1)
{
lean_object* v_val_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_val_3747_ = lean_ctor_get(v_a_3743_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3749_ = v_a_3743_;
v_isShared_3750_ = v_isSharedCheck_3759_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_val_3747_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3759_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3751_ = lean_box(0);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v_val_3747_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3752_);
v___x_3754_ = v___x_3749_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3756_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3754_);
v___x_3756_ = v___x_3745_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v___x_3760_; 
lean_del_object(v___x_3745_);
lean_dec(v_a_3743_);
lean_inc_ref(v_expectedType_3736_);
v___x_3760_ = l_Lean_Meta_whnfR(v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; uint8_t v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = l_Lean_Expr_isForall(v_a_3761_);
lean_dec(v_a_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3735_, v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; 
lean_inc_ref(v_expr_3735_);
v___x_3764_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3735_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
if (lean_obj_tag(v_a_3765_) == 1)
{
lean_object* v_val_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3804_; 
v_val_3766_ = lean_ctor_get(v_a_3765_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3768_ = v_a_3765_;
v_isShared_3769_ = v_isSharedCheck_3804_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_val_3766_);
lean_dec(v_a_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3804_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; 
lean_inc(v_a_3740_);
lean_inc_ref(v_a_3739_);
lean_inc(v_a_3738_);
lean_inc_ref(v_a_3737_);
lean_inc(v_val_3766_);
v___x_3770_ = lean_infer_type(v_val_3766_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
lean_inc_ref(v_expectedType_3736_);
v___x_3772_ = l_Lean_Meta_isExprDefEq(v_a_3771_, v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3787_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3787_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3787_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_unbox(v_a_3773_);
lean_dec(v_a_3773_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_del_object(v___x_3775_);
lean_del_object(v___x_3768_);
lean_dec(v_val_3766_);
v___x_3778_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3735_, v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v___x_3779_ = lean_box(0);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_val_3766_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3780_);
v___x_3782_ = v___x_3768_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v___x_3782_);
v___x_3784_ = v___x_3775_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
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
lean_del_object(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_a_3788_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3772_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3772_);
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
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_a_3796_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3770_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3770_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
else
{
lean_object* v___x_3805_; 
lean_dec(v_a_3765_);
v___x_3805_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3735_, v_expectedType_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3805_;
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_a_3806_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3764_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3764_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_a_3814_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3760_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3760_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v_expectedType_3736_);
lean_dec_ref(v_expr_3735_);
v_a_3823_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3742_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3742_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3831_, lean_object* v_expectedType_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3831_, v_expectedType_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3839_, lean_object* v_expectedType_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3839_, v_expectedType_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3871_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3871_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3871_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
switch(lean_obj_tag(v_a_3847_))
{
case 0:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
v___x_3851_ = lean_box(0);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3851_);
v___x_3853_ = v___x_3849_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
case 1:
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3866_; 
v_a_3855_ = lean_ctor_get(v_a_3847_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3857_ = v_a_3847_;
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v_a_3847_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_fst_3859_; lean_object* v___x_3861_; 
v_fst_3859_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_fst_3859_);
lean_dec(v_a_3855_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_fst_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_fst_3859_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3861_);
v___x_3863_ = v___x_3849_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
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
default: 
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = lean_box(2);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3867_);
v___x_3869_ = v___x_3849_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3846_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3846_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3880_, lean_object* v_expectedType_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Meta_coerce_x3f(v_expr_3880_, v_expectedType_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
return v_res_3887_;
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
