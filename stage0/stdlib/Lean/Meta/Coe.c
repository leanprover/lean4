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
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "coe_decl"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 217, 140, 88, 250, 134, 204, 64)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "auxiliary definition used to implement coercion (unfolded during elaboration)"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeDeclAttr"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 20, 115, 115, 128, 118, 26, 153)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr;
static const lean_string_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 308, .m_capacity = 308, .m_length = 307, .m_data = "Tags declarations to be unfolded during coercion elaboration.\n\nThis is mostly used to hide coercion implementation details and show the coerced result instead of\nan application of auxiliary definitions (e.g. `CoeT.coe`, `Coe.coe`). This attribute only works on\nreducible functions and instance projections.\n"};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(22) << 1) | 1)),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(112) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "autoLift"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(168, 70, 99, 132, 14, 255, 243, 87)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "Insert monadic lifts (i.e., `liftM` and coercions) when needed."};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(197, 184, 93, 140, 214, 99, 153, 189)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 146, 186, 152, 132, 76, 197)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(59, 34, 101, 209, 97, 81, 138, 47)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_coerceMonadLift_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "coeM"};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 146, 186, 152, 132, 76, 197)}};
static const lean_ctor_object l_Lean_Meta_coerceMonadLift_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(21, 111, 129, 2, 187, 243, 141, 114)}};
static const lean_object* l_Lean_Meta_coerceMonadLift_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_coerceMonadLift_x3f___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_25_ = ((lean_object*)(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_26_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_27_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_29_ = 0;
v___x_30_ = lean_box(2);
v___x_31_ = l_Lean_registerTagAttribute(v___x_26_, v___x_27_, v___f_25_, v___x_28_, v___x_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1(){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_37_ = ((lean_object*)(l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0));
v___x_38_ = l_Lean_addBuiltinDocString(v___x_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3(){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_));
v___x_68_ = ((lean_object*)(l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6));
v___x_69_ = l_Lean_addBuiltinDeclarationRanges(v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; 
v___x_279_ = ((size_t)5ULL);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_shift_left(v___x_280_, v___x_279_);
return v___x_281_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; 
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_284_ = lean_usize_sub(v___x_283_, v___x_282_);
return v___x_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_285_, size_t v_x_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_es_288_; lean_object* v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v_j_293_; lean_object* v___x_294_; 
v_es_288_ = lean_ctor_get(v_x_285_, 0);
v___x_289_ = lean_box(2);
v___x_290_ = ((size_t)5ULL);
v___x_291_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_292_ = lean_usize_land(v_x_286_, v___x_291_);
v_j_293_ = lean_usize_to_nat(v___x_292_);
v___x_294_ = lean_array_get_borrowed(v___x_289_, v_es_288_, v_j_293_);
lean_dec(v_j_293_);
switch(lean_obj_tag(v___x_294_))
{
case 0:
{
lean_object* v_key_295_; uint8_t v___x_296_; 
v_key_295_ = lean_ctor_get(v___x_294_, 0);
v___x_296_ = l_Lean_instBEqExtraModUse_beq(v_x_287_, v_key_295_);
return v___x_296_;
}
case 1:
{
lean_object* v_node_297_; size_t v___x_298_; 
v_node_297_ = lean_ctor_get(v___x_294_, 0);
v___x_298_ = lean_usize_shift_right(v_x_286_, v___x_290_);
v_x_285_ = v_node_297_;
v_x_286_ = v___x_298_;
goto _start;
}
default: 
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
}
else
{
lean_object* v_ks_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_ks_301_ = lean_ctor_get(v_x_285_, 0);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_301_, v___x_302_, v_x_287_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
size_t v_x_36461__boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_x_36461__boxed_307_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_res_308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_304_, v_x_36461__boxed_307_, v_x_306_);
lean_dec_ref(v_x_306_);
lean_dec_ref(v_x_304_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint64_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v___x_312_ = l_Lean_instHashableExtraModUse_hash(v_x_311_);
v___x_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_310_, v___x_313_, v_x_311_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_315_, v_x_316_);
lean_dec_ref(v_x_316_);
lean_dec_ref(v_x_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1));
v___x_322_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0));
v___x_323_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_330_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
lean_ctor_set(v___x_330_, 3, v___x_329_);
lean_ctor_set(v___x_330_, 4, v___x_329_);
lean_ctor_set(v___x_330_, 5, v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_cls_345_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15));
v___x_347_ = l_Lean_Name_append(v___x_346_, v_cls_345_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_358_, uint8_t v_isMeta_359_, lean_object* v_hint_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; lean_object* v_env_368_; uint8_t v_isExporting_369_; lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; lean_object* v_entry_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_367_ = lean_st_ref_get(v___y_365_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v_isExporting_369_ = lean_ctor_get_uint8(v_env_368_, sizeof(void*)*8);
lean_dec_ref(v_env_368_);
v___x_370_ = lean_st_ref_get(v___y_365_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
lean_inc(v_mod_358_);
v_entry_373_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_373_, 0, v_mod_358_);
lean_ctor_set_uint8(v_entry_373_, sizeof(void*)*1, v_isExporting_369_);
lean_ctor_set_uint8(v_entry_373_, sizeof(void*)*1 + 1, v_isMeta_359_);
v___x_374_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_375_ = lean_box(1);
v___x_376_ = lean_box(0);
v___x_421_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_372_, v___x_374_, v_env_371_, v___x_375_, v___x_376_);
v___x_422_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_421_, v_entry_373_);
lean_dec(v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v_options_423_; uint8_t v_hasTrace_424_; 
v_options_423_ = lean_ctor_get(v___y_364_, 2);
v_hasTrace_424_ = lean_ctor_get_uint8(v_options_423_, sizeof(void*)*1);
if (v_hasTrace_424_ == 0)
{
lean_dec(v_hint_360_);
lean_dec(v_mod_358_);
v___y_378_ = v___y_361_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_365_;
goto v___jp_377_;
}
else
{
lean_object* v_inheritedTraceOptions_425_; lean_object* v_cls_426_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_inheritedTraceOptions_425_ = lean_ctor_get(v___y_364_, 13);
v_cls_426_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_448_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
v___x_449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_425_, v_options_423_, v___x_448_);
if (v___x_449_ == 0)
{
lean_dec(v_hint_360_);
lean_dec(v_mod_358_);
v___y_378_ = v___y_361_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_365_;
goto v___jp_377_;
}
else
{
lean_object* v___x_450_; lean_object* v___y_452_; 
v___x_450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
if (v_isExporting_369_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23));
v___y_452_ = v___x_459_;
goto v___jp_451_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24));
v___y_452_ = v___x_460_;
goto v___jp_451_;
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc_ref(v___y_452_);
v___x_453_ = l_Lean_stringToMessageData(v___y_452_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_450_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
if (v_isMeta_359_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_435_ = v___x_456_;
v___y_436_ = v___x_457_;
goto v___jp_434_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22));
v___y_435_ = v___x_456_;
v___y_436_ = v___x_458_;
goto v___jp_434_;
}
}
}
v___jp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___y_428_);
lean_ctor_set(v___x_430_, 1, v___y_429_);
v___x_431_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_426_, v___x_430_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v_snd_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref(v___x_431_);
v_snd_433_ = lean_ctor_get(v_a_432_, 1);
lean_inc(v_snd_433_);
lean_dec(v_a_432_);
v___y_378_ = v_snd_433_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_365_;
goto v___jp_377_;
}
else
{
lean_dec_ref(v_entry_373_);
return v___x_431_;
}
}
v___jp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
lean_inc_ref(v___y_436_);
v___x_437_ = l_Lean_stringToMessageData(v___y_436_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___y_435_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_MessageData_ofName(v_mod_358_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_Name_isAnonymous(v_hint_360_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_445_ = l_Lean_MessageData_ofName(v_hint_360_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___y_428_ = v___x_442_;
v___y_429_ = v___x_446_;
goto v___jp_427_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v_hint_360_);
v___x_447_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_428_ = v___x_442_;
v___y_429_ = v___x_447_;
goto v___jp_427_;
}
}
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v_entry_373_);
lean_dec(v_hint_360_);
lean_dec(v_mod_358_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___y_361_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
v___jp_377_:
{
lean_object* v___x_381_; lean_object* v_toEnvExtension_382_; lean_object* v_env_383_; lean_object* v_nextMacroScope_384_; lean_object* v_ngen_385_; lean_object* v_auxDeclNGen_386_; lean_object* v_traceState_387_; lean_object* v_messages_388_; lean_object* v_infoState_389_; lean_object* v_snapshotTasks_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_419_; 
v___x_381_ = lean_st_ref_take(v___y_380_);
v_toEnvExtension_382_ = lean_ctor_get(v___x_374_, 0);
v_env_383_ = lean_ctor_get(v___x_381_, 0);
v_nextMacroScope_384_ = lean_ctor_get(v___x_381_, 1);
v_ngen_385_ = lean_ctor_get(v___x_381_, 2);
v_auxDeclNGen_386_ = lean_ctor_get(v___x_381_, 3);
v_traceState_387_ = lean_ctor_get(v___x_381_, 4);
v_messages_388_ = lean_ctor_get(v___x_381_, 6);
v_infoState_389_ = lean_ctor_get(v___x_381_, 7);
v_snapshotTasks_390_ = lean_ctor_get(v___x_381_, 8);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_381_, 5);
lean_dec(v_unused_420_);
v___x_392_ = v___x_381_;
v_isShared_393_ = v_isSharedCheck_419_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snapshotTasks_390_);
lean_inc(v_infoState_389_);
lean_inc(v_messages_388_);
lean_inc(v_traceState_387_);
lean_inc(v_auxDeclNGen_386_);
lean_inc(v_ngen_385_);
lean_inc(v_nextMacroScope_384_);
lean_inc(v_env_383_);
lean_dec(v___x_381_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_419_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_asyncMode_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v_asyncMode_394_ = lean_ctor_get(v_toEnvExtension_382_, 2);
v___x_395_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_374_, v_env_383_, v_entry_373_, v_asyncMode_394_, v___x_376_);
v___x_396_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 5, v___x_396_);
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_398_ = v___x_392_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_nextMacroScope_384_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_ngen_385_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_auxDeclNGen_386_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_traceState_387_);
lean_ctor_set(v_reuseFailAlloc_418_, 5, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 6, v_messages_388_);
lean_ctor_set(v_reuseFailAlloc_418_, 7, v_infoState_389_);
lean_ctor_set(v_reuseFailAlloc_418_, 8, v_snapshotTasks_390_);
v___x_398_ = v_reuseFailAlloc_418_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_mctx_401_; lean_object* v_zetaDeltaFVarIds_402_; lean_object* v_postponed_403_; lean_object* v_diag_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v___x_399_ = lean_st_ref_set(v___y_380_, v___x_398_);
v___x_400_ = lean_st_ref_take(v___y_379_);
v_mctx_401_ = lean_ctor_get(v___x_400_, 0);
v_zetaDeltaFVarIds_402_ = lean_ctor_get(v___x_400_, 2);
v_postponed_403_ = lean_ctor_get(v___x_400_, 3);
v_diag_404_ = lean_ctor_get(v___x_400_, 4);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_400_, 1);
lean_dec(v_unused_417_);
v___x_406_ = v___x_400_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_diag_404_);
lean_inc(v_postponed_403_);
lean_inc(v_zetaDeltaFVarIds_402_);
lean_inc(v_mctx_401_);
lean_dec(v___x_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_mctx_401_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_zetaDeltaFVarIds_402_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_postponed_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v_diag_404_);
v___x_410_ = v_reuseFailAlloc_415_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_st_ref_set(v___y_379_, v___x_410_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___y_378_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_464_, lean_object* v_isMeta_465_, lean_object* v_hint_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v_isMeta_boxed_473_; lean_object* v_res_474_; 
v_isMeta_boxed_473_ = lean_unbox(v_isMeta_465_);
v_res_474_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_464_, v_isMeta_boxed_473_, v_hint_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v_key_478_; lean_object* v_value_479_; lean_object* v_tail_480_; uint8_t v___x_481_; 
v_key_478_ = lean_ctor_get(v_x_476_, 0);
v_value_479_ = lean_ctor_get(v_x_476_, 1);
v_tail_480_ = lean_ctor_get(v_x_476_, 2);
v___x_481_ = lean_name_eq(v_key_478_, v_a_475_);
if (v___x_481_ == 0)
{
v_x_476_ = v_tail_480_;
goto _start;
}
else
{
lean_object* v___x_483_; 
lean_inc(v_value_479_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_value_479_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_484_, v_x_485_);
lean_dec(v_x_485_);
lean_dec(v_a_484_);
return v_res_486_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_487_; uint64_t v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1723u);
v___x_488_ = lean_uint64_of_nat(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_buckets_491_; lean_object* v___x_492_; uint64_t v___y_494_; 
v_buckets_491_ = lean_ctor_get(v_m_489_, 1);
v___x_492_ = lean_array_get_size(v_buckets_491_);
if (lean_obj_tag(v_a_490_) == 0)
{
uint64_t v___x_508_; 
v___x_508_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
v___y_494_ = v___x_508_;
goto v___jp_493_;
}
else
{
uint64_t v_hash_509_; 
v_hash_509_ = lean_ctor_get_uint64(v_a_490_, sizeof(void*)*2);
v___y_494_ = v_hash_509_;
goto v___jp_493_;
}
v___jp_493_:
{
uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v_fold_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_495_ = 32ULL;
v___x_496_ = lean_uint64_shift_right(v___y_494_, v___x_495_);
v_fold_497_ = lean_uint64_xor(v___y_494_, v___x_496_);
v___x_498_ = 16ULL;
v___x_499_ = lean_uint64_shift_right(v_fold_497_, v___x_498_);
v___x_500_ = lean_uint64_xor(v_fold_497_, v___x_499_);
v___x_501_ = lean_uint64_to_usize(v___x_500_);
v___x_502_ = lean_usize_of_nat(v___x_492_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_sub(v___x_502_, v___x_503_);
v___x_505_ = lean_usize_land(v___x_501_, v___x_504_);
v___x_506_ = lean_array_uget_borrowed(v_buckets_491_, v___x_505_);
v___x_507_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_490_, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_m_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_513_, lean_object* v_declName_514_, lean_object* v_as_515_, size_t v_sz_516_, size_t v_i_517_, lean_object* v_b_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_lt(v_i_517_, v_sz_516_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_declName_514_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_b_518_);
lean_ctor_set(v___x_526_, 1, v___y_519_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v_modules_529_; lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v_toImport_533_; lean_object* v_module_534_; uint8_t v___x_535_; lean_object* v___x_536_; 
v___x_528_ = l_Lean_Environment_header(v___x_513_);
v_modules_529_ = lean_ctor_get(v___x_528_, 3);
lean_inc_ref(v_modules_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_531_ = lean_array_uget_borrowed(v_as_515_, v_i_517_);
v___x_532_ = lean_array_get(v___x_530_, v_modules_529_, v_a_531_);
lean_dec_ref(v_modules_529_);
v_toImport_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_toImport_533_);
lean_dec(v___x_532_);
v_module_534_ = lean_ctor_get(v_toImport_533_, 0);
lean_inc(v_module_534_);
lean_dec_ref(v_toImport_533_);
v___x_535_ = 0;
lean_inc(v_declName_514_);
v___x_536_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_534_, v___x_535_, v_declName_514_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_snd_538_; lean_object* v___x_539_; size_t v___x_540_; size_t v___x_541_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref(v___x_536_);
v_snd_538_ = lean_ctor_get(v_a_537_, 1);
lean_inc(v_snd_538_);
lean_dec(v_a_537_);
v___x_539_ = lean_box(0);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_517_, v___x_540_);
v_i_517_ = v___x_541_;
v_b_518_ = v___x_539_;
v___y_519_ = v_snd_538_;
goto _start;
}
else
{
lean_dec(v_declName_514_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_543_, lean_object* v_declName_544_, lean_object* v_as_545_, lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
size_t v_sz_boxed_555_; size_t v_i_boxed_556_; lean_object* v_res_557_; 
v_sz_boxed_555_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_556_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_543_, v_declName_544_, v_as_545_, v_sz_boxed_555_, v_i_boxed_556_, v_b_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_as_545_);
lean_dec_ref(v___x_543_);
return v_res_557_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_561_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_562_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_561_, v___x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_565_, uint8_t v_isMeta_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_env_578_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___x_603_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_578_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_573_);
v___x_603_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_578_, v_declName_565_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_dec_ref(v_env_578_);
lean_dec(v_declName_565_);
goto v___jp_574_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_605_; lean_object* v_modules_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_val_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_val_604_);
lean_dec_ref(v___x_603_);
v___x_605_ = l_Lean_Environment_header(v_env_578_);
v_modules_606_ = lean_ctor_get(v___x_605_, 3);
lean_inc_ref(v_modules_606_);
lean_dec_ref(v___x_605_);
v___x_607_ = lean_array_get_size(v_modules_606_);
v___x_608_ = lean_nat_dec_lt(v_val_604_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec_ref(v_modules_606_);
lean_dec(v_val_604_);
lean_dec_ref(v_env_578_);
lean_dec(v_declName_565_);
goto v___jp_574_;
}
else
{
lean_object* v___x_609_; lean_object* v_env_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___y_614_; 
v___x_609_ = lean_st_ref_get(v___y_571_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v___x_611_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_612_ = lean_array_fget(v_modules_606_, v_val_604_);
lean_dec(v_val_604_);
lean_dec_ref(v_modules_606_);
if (v_isMeta_566_ == 0)
{
lean_dec_ref(v_env_610_);
v___y_614_ = v_isMeta_566_;
goto v___jp_613_;
}
else
{
uint8_t v___x_627_; 
lean_inc(v_declName_565_);
v___x_627_ = l_Lean_isMarkedMeta(v_env_610_, v_declName_565_);
if (v___x_627_ == 0)
{
v___y_614_ = v_isMeta_566_;
goto v___jp_613_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
v___y_614_ = v___x_628_;
goto v___jp_613_;
}
}
v___jp_613_:
{
lean_object* v_toImport_615_; lean_object* v_module_616_; lean_object* v___x_617_; 
v_toImport_615_ = lean_ctor_get(v___x_612_, 0);
lean_inc_ref(v_toImport_615_);
lean_dec(v___x_612_);
v_module_616_ = lean_ctor_get(v_toImport_615_, 0);
lean_inc(v_module_616_);
lean_dec_ref(v_toImport_615_);
lean_inc(v_declName_565_);
v___x_617_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_616_, v___y_614_, v_declName_565_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v_snd_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v___x_617_);
v_snd_619_ = lean_ctor_get(v_a_618_, 1);
lean_inc(v_snd_619_);
lean_dec(v_a_618_);
v___x_620_ = l_Lean_indirectModUseExt;
v___x_621_ = lean_box(1);
v___x_622_ = lean_box(0);
lean_inc_ref(v_env_578_);
v___x_623_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_611_, v___x_620_, v_env_578_, v___x_621_, v___x_622_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_623_, v_declName_565_);
lean_dec(v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_580_ = v_snd_619_;
v___y_581_ = v___x_625_;
goto v___jp_579_;
}
else
{
lean_object* v_val_626_; 
v_val_626_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_626_);
lean_dec_ref(v___x_624_);
v___y_580_ = v_snd_619_;
v___y_581_ = v_val_626_;
goto v___jp_579_;
}
}
else
{
lean_dec_ref(v_env_578_);
lean_dec(v_declName_565_);
return v___x_617_;
}
}
}
}
v___jp_574_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___y_567_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
v___jp_579_:
{
lean_object* v___x_582_; size_t v_sz_583_; size_t v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(0);
v_sz_583_ = lean_array_size(v___y_581_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_578_, v_declName_565_, v___y_581_, v_sz_583_, v___x_584_, v___x_582_, v___y_580_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v_env_578_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_602_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_602_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_600_; 
v_snd_590_ = lean_ctor_get(v_a_586_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_a_586_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v_a_586_, 0);
lean_dec(v_unused_601_);
v___x_592_ = v_a_586_;
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_dec(v_a_586_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_582_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_snd_590_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_595_);
v___x_597_ = v___x_588_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_629_, lean_object* v_isMeta_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
uint8_t v_isMeta_boxed_637_; lean_object* v_res_638_; 
v_isMeta_boxed_637_ = lean_unbox(v_isMeta_630_);
v_res_638_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_629_, v_isMeta_boxed_637_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___y_654_; lean_object* v_f_658_; uint8_t v___x_659_; 
v_f_658_ = l_Lean_Expr_getAppFn(v_e_646_);
v___x_659_ = l_Lean_Expr_isConst(v_f_658_);
if (v___x_659_ == 0)
{
lean_dec_ref(v_f_658_);
lean_dec_ref(v_e_646_);
v___y_654_ = v___y_647_;
goto v___jp_653_;
}
else
{
lean_object* v___x_660_; lean_object* v_env_661_; lean_object* v_declName_662_; uint8_t v___x_663_; 
v___x_660_ = lean_st_ref_get(v___y_651_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_660_);
v_declName_662_ = l_Lean_Expr_constName_x21(v_f_658_);
lean_dec_ref(v_f_658_);
lean_inc(v_declName_662_);
v___x_663_ = l_Lean_Meta_isCoeDecl(v_env_661_, v_declName_662_);
if (v___x_663_ == 0)
{
lean_dec(v_declName_662_);
lean_dec_ref(v_e_646_);
v___y_654_ = v___y_647_;
goto v___jp_653_;
}
else
{
lean_object* v___x_664_; 
lean_inc(v_declName_662_);
lean_inc_ref(v_e_646_);
v___x_664_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_646_, v_declName_662_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = 0;
v___x_667_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_665_, v___x_666_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_720_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
v_snd_669_ = lean_ctor_get(v_a_668_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_668_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_a_668_, 0);
lean_dec(v_unused_721_);
v___x_671_ = v_a_668_;
v_isShared_672_ = v_isSharedCheck_720_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_dec(v_a_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_720_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; 
lean_inc_ref(v_e_646_);
v___x_673_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_646_, v___x_666_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_711_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_711_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_711_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_711_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_a_674_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_710_; 
v_val_678_ = lean_ctor_get(v_a_674_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_710_ == 0)
{
v___x_680_ = v_a_674_;
v_isShared_681_ = v_isSharedCheck_710_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v_a_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_710_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___y_683_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_695_ = lean_name_eq(v_declName_662_, v___x_694_);
lean_dec(v_declName_662_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_e_646_);
v___y_683_ = v_snd_669_;
goto v___jp_682_;
}
else
{
lean_object* v_dummy_696_; lean_object* v_nargs_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_dummy_696_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_697_ = l_Lean_Expr_getAppNumArgs(v_e_646_);
lean_inc(v_nargs_697_);
v___x_698_ = lean_mk_array(v_nargs_697_, v_dummy_696_);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_sub(v_nargs_697_, v___x_699_);
lean_dec(v_nargs_697_);
v___x_701_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_646_, v___x_698_, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(2u);
v___x_703_ = lean_array_get_size(v___x_701_);
v___x_704_ = lean_nat_dec_lt(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_701_);
v___y_683_ = v_snd_669_;
goto v___jp_682_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_array_fget(v___x_701_, v___x_702_);
lean_dec_ref(v___x_701_);
v___x_706_ = l_Lean_Expr_getAppFn(v___x_705_);
lean_dec(v___x_705_);
v___x_707_ = l_Lean_Expr_isConst(v___x_706_);
if (v___x_707_ == 0)
{
lean_dec_ref(v___x_706_);
v___y_683_ = v_snd_669_;
goto v___jp_682_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Lean_Expr_constName_x21(v___x_706_);
lean_dec_ref(v___x_706_);
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_snd_669_);
v___y_683_ = v___x_709_;
goto v___jp_682_;
}
}
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_Expr_headBeta(v_val_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_693_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___y_683_);
lean_ctor_set(v___x_671_, 0, v___x_686_);
v___x_688_ = v___x_671_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___y_683_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_688_);
v___x_690_ = v___x_676_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_676_);
lean_dec(v_a_674_);
lean_del_object(v___x_671_);
lean_dec(v_declName_662_);
lean_dec_ref(v_e_646_);
v___y_654_ = v_snd_669_;
goto v___jp_653_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_del_object(v___x_671_);
lean_dec(v_snd_669_);
lean_dec(v_declName_662_);
lean_dec_ref(v_e_646_);
v_a_712_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_673_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_673_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_declName_662_);
lean_dec_ref(v_e_646_);
v_a_722_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_667_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_667_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_declName_662_);
lean_dec(v___y_647_);
lean_dec_ref(v_e_646_);
v_a_730_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_664_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_664_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___y_654_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_expandCoe___lam__1(v_e_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(lean_object* v_k_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_747_);
v___x_755_ = lean_apply_8(v_k_746_, v_b_749_, v___y_747_, v___y_748_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(lean_object* v_k_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_756_, v___y_757_, v___y_758_, v_b_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_757_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(lean_object* v_name_766_, uint8_t v_bi_767_, lean_object* v_type_768_, lean_object* v_k_769_, uint8_t v_kind_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; 
lean_inc(v___y_771_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_778_, 0, v_k_769_);
lean_closure_set(v___f_778_, 1, v___y_771_);
lean_closure_set(v___f_778_, 2, v___y_772_);
v___x_779_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_766_, v_bi_767_, v_type_768_, v___f_778_, v_kind_770_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_779_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_779_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(lean_object* v_name_796_, lean_object* v_bi_797_, lean_object* v_type_798_, lean_object* v_k_799_, lean_object* v_kind_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v_bi_boxed_808_; uint8_t v_kind_boxed_809_; lean_object* v_res_810_; 
v_bi_boxed_808_ = lean_unbox(v_bi_797_);
v_kind_boxed_809_ = lean_unbox(v_kind_800_);
v_res_810_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_796_, v_bi_boxed_808_, v_type_798_, v_k_799_, v_kind_boxed_809_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_801_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(lean_object* v___x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_811_);
lean_ctor_set(v___x_818_, 1, v___y_812_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(lean_object* v_name_828_, lean_object* v_type_829_, lean_object* v_val_830_, lean_object* v_k_831_, uint8_t v_nondep_832_, uint8_t v_kind_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___f_841_; lean_object* v___x_842_; 
lean_inc(v___y_834_);
v___f_841_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_841_, 0, v_k_831_);
lean_closure_set(v___f_841_, 1, v___y_834_);
lean_closure_set(v___f_841_, 2, v___y_835_);
v___x_842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_828_, v_type_829_, v_val_830_, v___f_841_, v_nondep_832_, v_kind_833_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_842_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_842_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(lean_object* v_name_859_, lean_object* v_type_860_, lean_object* v_val_861_, lean_object* v_k_862_, lean_object* v_nondep_863_, lean_object* v_kind_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_nondep_boxed_872_; uint8_t v_kind_boxed_873_; lean_object* v_res_874_; 
v_nondep_boxed_872_ = lean_unbox(v_nondep_863_);
v_kind_boxed_873_ = lean_unbox(v_kind_864_);
v_res_874_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_859_, v_type_860_, v_val_861_, v_k_862_, v_nondep_boxed_872_, v_kind_boxed_873_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_865_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(lean_object* v_a_875_, lean_object* v_b_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_dec(v_b_876_);
lean_dec_ref(v_a_875_);
return v_x_877_;
}
else
{
lean_object* v_key_878_; lean_object* v_value_879_; lean_object* v_tail_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_892_; 
v_key_878_ = lean_ctor_get(v_x_877_, 0);
v_value_879_ = lean_ctor_get(v_x_877_, 1);
v_tail_880_ = lean_ctor_get(v_x_877_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_892_ == 0)
{
v___x_882_ = v_x_877_;
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_tail_880_);
lean_inc(v_value_879_);
lean_inc(v_key_878_);
lean_dec(v_x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_ExprStructEq_beq(v_key_878_, v_a_875_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_875_, v_b_876_, v_tail_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 2, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_key_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_value_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v___x_890_; 
lean_dec(v_value_879_);
lean_dec(v_key_878_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_b_876_);
lean_ctor_set(v___x_882_, 0, v_a_875_);
v___x_890_ = v___x_882_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_875_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_b_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_tail_880_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(lean_object* v_a_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
else
{
lean_object* v_key_896_; lean_object* v_tail_897_; uint8_t v___x_898_; 
v_key_896_ = lean_ctor_get(v_x_894_, 0);
v_tail_897_ = lean_ctor_get(v_x_894_, 2);
v___x_898_ = l_Lean_ExprStructEq_beq(v_key_896_, v_a_893_);
if (v___x_898_ == 0)
{
v_x_894_ = v_tail_897_;
goto _start;
}
else
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(lean_object* v_a_900_, lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_900_, v_x_901_);
lean_dec(v_x_901_);
lean_dec_ref(v_a_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
return v_x_904_;
}
else
{
lean_object* v_key_906_; lean_object* v_value_907_; lean_object* v_tail_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_931_; 
v_key_906_ = lean_ctor_get(v_x_905_, 0);
v_value_907_ = lean_ctor_get(v_x_905_, 1);
v_tail_908_ = lean_ctor_get(v_x_905_, 2);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_931_ == 0)
{
v___x_910_ = v_x_905_;
v_isShared_911_ = v_isSharedCheck_931_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_tail_908_);
lean_inc(v_value_907_);
lean_inc(v_key_906_);
lean_dec(v_x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_931_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v_fold_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_912_ = lean_array_get_size(v_x_904_);
v___x_913_ = l_Lean_ExprStructEq_hash(v_key_906_);
v___x_914_ = 32ULL;
v___x_915_ = lean_uint64_shift_right(v___x_913_, v___x_914_);
v_fold_916_ = lean_uint64_xor(v___x_913_, v___x_915_);
v___x_917_ = 16ULL;
v___x_918_ = lean_uint64_shift_right(v_fold_916_, v___x_917_);
v___x_919_ = lean_uint64_xor(v_fold_916_, v___x_918_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = lean_usize_of_nat(v___x_912_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_sub(v___x_921_, v___x_922_);
v___x_924_ = lean_usize_land(v___x_920_, v___x_923_);
v___x_925_ = lean_array_uget_borrowed(v_x_904_, v___x_924_);
lean_inc(v___x_925_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v___x_925_);
v___x_927_ = v___x_910_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_key_906_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_value_907_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v___x_925_);
v___x_927_ = v_reuseFailAlloc_930_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_array_uset(v_x_904_, v___x_924_, v___x_927_);
v_x_904_ = v___x_928_;
v_x_905_ = v_tail_908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(lean_object* v_i_932_, lean_object* v_source_933_, lean_object* v_target_934_){
_start:
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_array_get_size(v_source_933_);
v___x_936_ = lean_nat_dec_lt(v_i_932_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v_source_933_);
lean_dec(v_i_932_);
return v_target_934_;
}
else
{
lean_object* v_es_937_; lean_object* v___x_938_; lean_object* v_source_939_; lean_object* v_target_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_es_937_ = lean_array_fget(v_source_933_, v_i_932_);
v___x_938_ = lean_box(0);
v_source_939_ = lean_array_fset(v_source_933_, v_i_932_, v___x_938_);
v_target_940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_934_, v_es_937_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_i_932_, v___x_941_);
lean_dec(v_i_932_);
v_i_932_ = v___x_942_;
v_source_933_ = v_source_939_;
v_target_934_ = v_target_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(lean_object* v_data_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_nbuckets_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_945_ = lean_array_get_size(v_data_944_);
v___x_946_ = lean_unsigned_to_nat(2u);
v_nbuckets_947_ = lean_nat_mul(v___x_945_, v___x_946_);
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_box(0);
v___x_950_ = lean_mk_array(v_nbuckets_947_, v___x_949_);
v___x_951_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_948_, v_data_944_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_m_952_, lean_object* v_a_953_, lean_object* v_b_954_){
_start:
{
lean_object* v_size_955_; lean_object* v_buckets_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_999_; 
v_size_955_ = lean_ctor_get(v_m_952_, 0);
v_buckets_956_ = lean_ctor_get(v_m_952_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_m_952_);
if (v_isSharedCheck_999_ == 0)
{
v___x_958_ = v_m_952_;
v_isShared_959_ = v_isSharedCheck_999_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_buckets_956_);
lean_inc(v_size_955_);
lean_dec(v_m_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_999_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v___x_963_; uint64_t v_fold_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v_bkt_973_; uint8_t v___x_974_; 
v___x_960_ = lean_array_get_size(v_buckets_956_);
v___x_961_ = l_Lean_ExprStructEq_hash(v_a_953_);
v___x_962_ = 32ULL;
v___x_963_ = lean_uint64_shift_right(v___x_961_, v___x_962_);
v_fold_964_ = lean_uint64_xor(v___x_961_, v___x_963_);
v___x_965_ = 16ULL;
v___x_966_ = lean_uint64_shift_right(v_fold_964_, v___x_965_);
v___x_967_ = lean_uint64_xor(v_fold_964_, v___x_966_);
v___x_968_ = lean_uint64_to_usize(v___x_967_);
v___x_969_ = lean_usize_of_nat(v___x_960_);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_sub(v___x_969_, v___x_970_);
v___x_972_ = lean_usize_land(v___x_968_, v___x_971_);
v_bkt_973_ = lean_array_uget_borrowed(v_buckets_956_, v___x_972_);
v___x_974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_953_, v_bkt_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v_size_x27_976_; lean_object* v___x_977_; lean_object* v_buckets_x27_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v_size_x27_976_ = lean_nat_add(v_size_955_, v___x_975_);
lean_dec(v_size_955_);
lean_inc(v_bkt_973_);
v___x_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_977_, 0, v_a_953_);
lean_ctor_set(v___x_977_, 1, v_b_954_);
lean_ctor_set(v___x_977_, 2, v_bkt_973_);
v_buckets_x27_978_ = lean_array_uset(v_buckets_956_, v___x_972_, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(4u);
v___x_980_ = lean_nat_mul(v_size_x27_976_, v___x_979_);
v___x_981_ = lean_unsigned_to_nat(3u);
v___x_982_ = lean_nat_div(v___x_980_, v___x_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_array_get_size(v_buckets_x27_978_);
v___x_984_ = lean_nat_dec_le(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
if (v___x_984_ == 0)
{
lean_object* v_val_985_; lean_object* v___x_987_; 
v_val_985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_978_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_val_985_);
lean_ctor_set(v___x_958_, 0, v_size_x27_976_);
v___x_987_ = v___x_958_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_size_x27_976_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_val_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_990_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_buckets_x27_978_);
lean_ctor_set(v___x_958_, 0, v_size_x27_976_);
v___x_990_ = v___x_958_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_size_x27_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_buckets_x27_978_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_object* v___x_992_; lean_object* v_buckets_x27_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_bkt_973_);
v___x_992_ = lean_box(0);
v_buckets_x27_993_ = lean_array_uset(v_buckets_956_, v___x_972_, v___x_992_);
v___x_994_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_953_, v_b_954_, v_bkt_973_);
v___x_995_ = lean_array_uset(v_buckets_x27_993_, v___x_972_, v___x_994_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_995_);
v___x_997_ = v___x_958_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_size_955_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1000_, lean_object* v_e_1001_, lean_object* v_fst_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_st_ref_take(v_a_1000_);
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_1004_, v_e_1001_, v_fst_1002_);
v___x_1006_ = lean_st_ref_set(v_a_1000_, v___x_1005_);
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1008_, lean_object* v_e_1009_, lean_object* v_fst_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1008_, v_e_1009_, v_fst_1010_);
lean_dec(v_a_1008_);
return v_res_1012_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Lean_maxRecDepthErrorMessage;
v___x_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
v___x_1021_ = l_Lean_MessageData_ofFormat(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
v___x_1023_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2));
v___x_1024_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(lean_object* v_ref_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_ref_1025_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_ref_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(lean_object* v_x_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___y_1042_; lean_object* v_fileName_1059_; lean_object* v_fileMap_1060_; lean_object* v_options_1061_; lean_object* v_currRecDepth_1062_; lean_object* v_maxRecDepth_1063_; lean_object* v_ref_1064_; lean_object* v_currNamespace_1065_; lean_object* v_openDecls_1066_; lean_object* v_initHeartbeats_1067_; lean_object* v_maxHeartbeats_1068_; lean_object* v_quotContext_1069_; lean_object* v_currMacroScope_1070_; uint8_t v_diag_1071_; lean_object* v_cancelTk_x3f_1072_; uint8_t v_suppressElabErrors_1073_; lean_object* v_inheritedTraceOptions_1074_; uint8_t v___x_1075_; 
v_fileName_1059_ = lean_ctor_get(v___y_1038_, 0);
v_fileMap_1060_ = lean_ctor_get(v___y_1038_, 1);
v_options_1061_ = lean_ctor_get(v___y_1038_, 2);
v_currRecDepth_1062_ = lean_ctor_get(v___y_1038_, 3);
v_maxRecDepth_1063_ = lean_ctor_get(v___y_1038_, 4);
v_ref_1064_ = lean_ctor_get(v___y_1038_, 5);
v_currNamespace_1065_ = lean_ctor_get(v___y_1038_, 6);
v_openDecls_1066_ = lean_ctor_get(v___y_1038_, 7);
v_initHeartbeats_1067_ = lean_ctor_get(v___y_1038_, 8);
v_maxHeartbeats_1068_ = lean_ctor_get(v___y_1038_, 9);
v_quotContext_1069_ = lean_ctor_get(v___y_1038_, 10);
v_currMacroScope_1070_ = lean_ctor_get(v___y_1038_, 11);
v_diag_1071_ = lean_ctor_get_uint8(v___y_1038_, sizeof(void*)*14);
v_cancelTk_x3f_1072_ = lean_ctor_get(v___y_1038_, 12);
v_suppressElabErrors_1073_ = lean_ctor_get_uint8(v___y_1038_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1074_ = lean_ctor_get(v___y_1038_, 13);
v___x_1075_ = lean_nat_dec_eq(v_currRecDepth_1062_, v_maxRecDepth_1063_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_currRecDepth_1062_, v___x_1076_);
lean_inc_ref(v_inheritedTraceOptions_1074_);
lean_inc(v_cancelTk_x3f_1072_);
lean_inc(v_currMacroScope_1070_);
lean_inc(v_quotContext_1069_);
lean_inc(v_maxHeartbeats_1068_);
lean_inc(v_initHeartbeats_1067_);
lean_inc(v_openDecls_1066_);
lean_inc(v_currNamespace_1065_);
lean_inc(v_ref_1064_);
lean_inc(v_maxRecDepth_1063_);
lean_inc_ref(v_options_1061_);
lean_inc_ref(v_fileMap_1060_);
lean_inc_ref(v_fileName_1059_);
v___x_1078_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1078_, 0, v_fileName_1059_);
lean_ctor_set(v___x_1078_, 1, v_fileMap_1060_);
lean_ctor_set(v___x_1078_, 2, v_options_1061_);
lean_ctor_set(v___x_1078_, 3, v___x_1077_);
lean_ctor_set(v___x_1078_, 4, v_maxRecDepth_1063_);
lean_ctor_set(v___x_1078_, 5, v_ref_1064_);
lean_ctor_set(v___x_1078_, 6, v_currNamespace_1065_);
lean_ctor_set(v___x_1078_, 7, v_openDecls_1066_);
lean_ctor_set(v___x_1078_, 8, v_initHeartbeats_1067_);
lean_ctor_set(v___x_1078_, 9, v_maxHeartbeats_1068_);
lean_ctor_set(v___x_1078_, 10, v_quotContext_1069_);
lean_ctor_set(v___x_1078_, 11, v_currMacroScope_1070_);
lean_ctor_set(v___x_1078_, 12, v_cancelTk_x3f_1072_);
lean_ctor_set(v___x_1078_, 13, v_inheritedTraceOptions_1074_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*14, v_diag_1071_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*14 + 1, v_suppressElabErrors_1073_);
lean_inc(v___y_1039_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1034_);
v___x_1079_ = lean_apply_7(v_x_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___x_1078_, v___y_1039_, lean_box(0));
v___y_1042_ = v___x_1079_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1080_; 
lean_dec(v___y_1035_);
lean_dec_ref(v_x_1033_);
lean_inc(v_ref_1064_);
v___x_1080_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_1064_);
v___y_1042_ = v___x_1080_;
goto v___jp_1041_;
}
v___jp_1041_:
{
if (lean_obj_tag(v___y_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___y_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___y_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___y_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___y_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v___y_1042_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___y_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___y_1042_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___y_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
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
lean_dec_ref(v_fst_1199_);
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
lean_dec_ref(v_fst_1199_);
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
lean_dec_ref(v_e_x3f_1223_);
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
lean_object* v_binderName_1249_; lean_object* v_binderType_1250_; lean_object* v_body_1251_; uint8_t v_binderInfo_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_binderName_1249_ = lean_ctor_get(v_e_1241_, 0);
lean_inc(v_binderName_1249_);
v_binderType_1250_ = lean_ctor_get(v_e_1241_, 1);
lean_inc_ref(v_binderType_1250_);
v_body_1251_ = lean_ctor_get(v_e_1241_, 2);
lean_inc_ref(v_body_1251_);
v_binderInfo_1252_ = lean_ctor_get_uint8(v_e_1241_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1241_);
v___x_1253_ = lean_expr_instantiate_rev(v_binderType_1250_, v_fvars_1240_);
lean_dec_ref(v_binderType_1250_);
lean_inc_ref(v_post_1236_);
lean_inc_ref(v_pre_1235_);
v___x_1254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1235_, v_post_1236_, v_usedLetOnly_1237_, v_skipConstInApp_1238_, v_skipInstances_1239_, v___x_1253_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v_fst_1256_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1257_);
lean_dec(v_a_1255_);
v___x_1258_ = lean_box(v_usedLetOnly_1237_);
v___x_1259_ = lean_box(v_skipConstInApp_1238_);
v___x_1260_ = lean_box(v_skipInstances_1239_);
v___f_1261_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1261_, 0, v_fvars_1240_);
lean_closure_set(v___f_1261_, 1, v_pre_1235_);
lean_closure_set(v___f_1261_, 2, v_post_1236_);
lean_closure_set(v___f_1261_, 3, v___x_1258_);
lean_closure_set(v___f_1261_, 4, v___x_1259_);
lean_closure_set(v___f_1261_, 5, v___x_1260_);
lean_closure_set(v___f_1261_, 6, v_body_1251_);
v___x_1262_ = 0;
v___x_1263_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1249_, v_binderInfo_1252_, v_fst_1256_, v___f_1261_, v___x_1262_, v_a_1242_, v_snd_1257_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1263_;
}
else
{
lean_dec_ref(v_body_1251_);
lean_dec(v_binderName_1249_);
lean_dec_ref(v_fvars_1240_);
lean_dec_ref(v_post_1236_);
lean_dec_ref(v_pre_1235_);
return v___x_1254_;
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
lean_dec_ref(v___x_1265_);
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
lean_dec_ref(v___x_1272_);
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
lean_object* v_declName_1333_; lean_object* v_type_1334_; lean_object* v_value_1335_; lean_object* v_body_1336_; uint8_t v_nondep_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_declName_1333_ = lean_ctor_get(v_e_1325_, 0);
lean_inc(v_declName_1333_);
v_type_1334_ = lean_ctor_get(v_e_1325_, 1);
lean_inc_ref(v_type_1334_);
v_value_1335_ = lean_ctor_get(v_e_1325_, 2);
lean_inc_ref(v_value_1335_);
v_body_1336_ = lean_ctor_get(v_e_1325_, 3);
lean_inc_ref(v_body_1336_);
v_nondep_1337_ = lean_ctor_get_uint8(v_e_1325_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1325_);
v___x_1338_ = lean_expr_instantiate_rev(v_type_1334_, v_fvars_1324_);
lean_dec_ref(v_type_1334_);
lean_inc_ref(v_post_1320_);
lean_inc_ref(v_pre_1319_);
v___x_1339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v___x_1338_, v_a_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v_fst_1341_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_fst_1341_);
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
lean_inc(v_snd_1342_);
lean_dec(v_a_1340_);
v___x_1343_ = lean_expr_instantiate_rev(v_value_1335_, v_fvars_1324_);
lean_dec_ref(v_value_1335_);
lean_inc_ref(v_post_1320_);
lean_inc_ref(v_pre_1319_);
v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1319_, v_post_1320_, v_usedLetOnly_1321_, v_skipConstInApp_1322_, v_skipInstances_1323_, v___x_1343_, v_a_1326_, v_snd_1342_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1344_);
v_fst_1346_ = lean_ctor_get(v_a_1345_, 0);
lean_inc(v_fst_1346_);
v_snd_1347_ = lean_ctor_get(v_a_1345_, 1);
lean_inc(v_snd_1347_);
lean_dec(v_a_1345_);
v___x_1348_ = lean_box(v_usedLetOnly_1321_);
v___x_1349_ = lean_box(v_skipConstInApp_1322_);
v___x_1350_ = lean_box(v_skipInstances_1323_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1351_, 0, v_fvars_1324_);
lean_closure_set(v___f_1351_, 1, v_pre_1319_);
lean_closure_set(v___f_1351_, 2, v_post_1320_);
lean_closure_set(v___f_1351_, 3, v___x_1348_);
lean_closure_set(v___f_1351_, 4, v___x_1349_);
lean_closure_set(v___f_1351_, 5, v___x_1350_);
lean_closure_set(v___f_1351_, 6, v_body_1336_);
v___x_1352_ = 0;
v___x_1353_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_1333_, v_fst_1341_, v_fst_1346_, v___f_1351_, v_nondep_1337_, v___x_1352_, v_a_1326_, v_snd_1347_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1353_;
}
else
{
lean_dec(v_fst_1341_);
lean_dec_ref(v_body_1336_);
lean_dec(v_declName_1333_);
lean_dec_ref(v_fvars_1324_);
lean_dec_ref(v_post_1320_);
lean_dec_ref(v_pre_1319_);
return v___x_1344_;
}
}
else
{
lean_dec_ref(v_body_1336_);
lean_dec_ref(v_value_1335_);
lean_dec(v_declName_1333_);
lean_dec_ref(v_fvars_1324_);
lean_dec_ref(v_post_1320_);
lean_dec_ref(v_pre_1319_);
return v___x_1339_;
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
lean_dec_ref(v___x_1355_);
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
lean_dec_ref(v___x_1361_);
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
lean_object* v_v_1390_; lean_object* v___x_1391_; 
v_v_1390_ = lean_array_uget_borrowed(v_bs_1379_, v_i_1378_);
lean_inc(v_v_1390_);
lean_inc_ref(v_post_1373_);
lean_inc_ref(v_pre_1372_);
v___x_1391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1372_, v_post_1373_, v_usedLetOnly_1374_, v_skipConstInApp_1375_, v_skipInstances_1376_, v_v_1390_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v___x_1395_; lean_object* v_bs_x27_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref(v___x_1391_);
v_fst_1393_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_fst_1393_);
v_snd_1394_ = lean_ctor_get(v_a_1392_, 1);
lean_inc(v_snd_1394_);
lean_dec(v_a_1392_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v_bs_x27_1396_ = lean_array_uset(v_bs_1379_, v_i_1378_, v___x_1395_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1378_, v___x_1397_);
v___x_1399_ = lean_array_uset(v_bs_x27_1396_, v_i_1378_, v_fst_1393_);
v_i_1378_ = v___x_1398_;
v_bs_1379_ = v___x_1399_;
v___y_1381_ = v_snd_1394_;
goto _start;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_bs_1379_);
lean_dec_ref(v_post_1373_);
lean_dec_ref(v_pre_1372_);
v_a_1401_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1391_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1391_);
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
lean_dec_ref(v_fst_1494_);
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
lean_dec_ref(v_fst_1494_);
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
lean_dec_ref(v_x_1545_);
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
lean_dec_ref(v___x_1565_);
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
lean_dec_ref(v___x_1580_);
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
lean_dec_ref(v___x_1584_);
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
lean_dec_ref(v___x_1607_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v_pre_1618_, lean_object* v_e_1619_, lean_object* v_post_1620_, uint8_t v_usedLetOnly_1621_, uint8_t v_skipConstInApp_1622_, uint8_t v_skipInstances_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_pre_1618_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc_ref(v_e_1619_);
v___x_1631_ = lean_apply_7(v_pre_1618_, v_e_1619_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
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
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_pre_1618_);
v_e_1681_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc_ref(v_e_1681_);
lean_dec_ref(v_fst_1636_);
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
lean_dec_ref(v_e_1619_);
v_e_1688_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc_ref(v_e_1688_);
lean_dec_ref(v_fst_1636_);
v___x_1689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v_e_1688_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1689_;
}
default: 
{
lean_object* v_e_x3f_1690_; 
lean_del_object(v___x_1639_);
lean_del_object(v___x_1634_);
v_e_x3f_1690_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc(v_e_x3f_1690_);
lean_dec_ref(v_fst_1636_);
if (lean_obj_tag(v_e_x3f_1690_) == 0)
{
v___y_1642_ = v_e_1619_;
goto v___jp_1641_;
}
else
{
lean_object* v_val_1691_; 
lean_dec_ref(v_e_1619_);
v_val_1691_ = lean_ctor_get(v_e_x3f_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v_e_x3f_1690_);
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
v___x_1644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___x_1643_, v___y_1642_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1644_;
}
case 6:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___x_1645_, v___y_1642_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1646_;
}
case 8:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___x_1647_, v___y_1642_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
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
v___x_1654_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_1623_, v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v___y_1642_, v___x_1651_, v___x_1653_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1654_;
}
case 10:
{
lean_object* v_data_1655_; lean_object* v_expr_1656_; lean_object* v___x_1657_; 
v_data_1655_ = lean_ctor_get(v___y_1642_, 0);
v_expr_1656_ = lean_ctor_get(v___y_1642_, 1);
lean_inc_ref(v_expr_1656_);
lean_inc_ref(v_post_1620_);
lean_inc_ref(v_pre_1618_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v_expr_1656_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; size_t v___x_1661_; size_t v___x_1662_; uint8_t v___x_1663_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
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
lean_dec_ref(v___y_1642_);
v___x_1664_ = l_Lean_Expr_mdata___override(v_data_1655_, v_fst_1659_);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___x_1664_, v___y_1624_, v_snd_1660_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_fst_1659_);
v___x_1666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___y_1642_, v___y_1624_, v_snd_1660_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1666_;
}
}
else
{
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_pre_1618_);
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
lean_inc_ref(v_post_1620_);
lean_inc_ref(v_pre_1618_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v_struct_1669_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_fst_1672_; lean_object* v_snd_1673_; size_t v___x_1674_; size_t v___x_1675_; uint8_t v___x_1676_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
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
lean_dec_ref(v___y_1642_);
v___x_1677_ = l_Lean_Expr_proj___override(v_typeName_1667_, v_idx_1668_, v_fst_1672_);
v___x_1678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___x_1677_, v___y_1624_, v_snd_1673_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
lean_dec(v_fst_1672_);
v___x_1679_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___y_1642_, v___y_1624_, v_snd_1673_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1679_;
}
}
else
{
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_pre_1618_);
return v___x_1670_;
}
}
default: 
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1618_, v_post_1620_, v_usedLetOnly_1621_, v_skipConstInApp_1622_, v_skipInstances_1623_, v___y_1642_, v___y_1624_, v_snd_1637_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
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
lean_dec_ref(v_post_1620_);
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_pre_1618_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v_pre_1702_, lean_object* v_e_1703_, lean_object* v_post_1704_, lean_object* v_usedLetOnly_1705_, lean_object* v_skipConstInApp_1706_, lean_object* v_skipInstances_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_usedLetOnly_boxed_1715_; uint8_t v_skipConstInApp_boxed_1716_; uint8_t v_skipInstances_boxed_1717_; lean_object* v_res_1718_; 
v_usedLetOnly_boxed_1715_ = lean_unbox(v_usedLetOnly_1705_);
v_skipConstInApp_boxed_1716_ = lean_unbox(v_skipConstInApp_1706_);
v_skipInstances_boxed_1717_ = lean_unbox(v_skipInstances_1707_);
v_res_1718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v_pre_1702_, v_e_1703_, v_post_1704_, v_usedLetOnly_boxed_1715_, v_skipConstInApp_boxed_1716_, v_skipInstances_boxed_1717_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
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
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1787_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1787_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1787_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1786_; 
v_fst_1738_ = lean_ctor_get(v_a_1734_, 0);
v_snd_1739_ = lean_ctor_get(v_a_1734_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1734_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1741_ = v_a_1734_;
v_isShared_1742_ = v_isSharedCheck_1786_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_inc(v_fst_1738_);
lean_dec(v_a_1734_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1786_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_1738_, v_e_1724_);
lean_dec(v_fst_1738_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1741_);
lean_del_object(v___x_1736_);
v___x_1744_ = lean_box(v_usedLetOnly_1721_);
v___x_1745_ = lean_box(v_skipConstInApp_1722_);
v___x_1746_ = lean_box(v_skipInstances_1723_);
lean_inc_ref(v_e_1724_);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1747_, 0, v_pre_1719_);
lean_closure_set(v___f_1747_, 1, v_e_1724_);
lean_closure_set(v___f_1747_, 2, v_post_1720_);
lean_closure_set(v___f_1747_, 3, v___x_1744_);
lean_closure_set(v___f_1747_, 4, v___x_1745_);
lean_closure_set(v___f_1747_, 5, v___x_1746_);
v___x_1748_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_1747_, v_a_1725_, v_snd_1739_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
v_fst_1750_ = lean_ctor_get(v_a_1749_, 0);
lean_inc_n(v_fst_1750_, 2);
v_snd_1751_ = lean_ctor_get(v_a_1749_, 1);
lean_inc(v_snd_1751_);
lean_dec(v_a_1749_);
lean_inc(v_a_1725_);
v___f_1752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1752_, 0, v_a_1725_);
lean_closure_set(v___f_1752_, 1, v_e_1724_);
lean_closure_set(v___f_1752_, 2, v_fst_1750_);
v___x_1753_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1752_, v_snd_1751_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1770_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1770_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1770_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_snd_1758_ = lean_ctor_get(v_a_1754_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_a_1754_, 0);
lean_dec(v_unused_1769_);
v___x_1760_ = v_a_1754_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snd_1758_);
lean_dec(v_a_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_fst_1750_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_fst_1750_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_snd_1758_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1763_);
v___x_1765_ = v___x_1756_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_fst_1750_);
v_a_1771_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1753_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1753_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_dec_ref(v_e_1724_);
return v___x_1748_;
}
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1781_; 
lean_dec_ref(v_e_1724_);
lean_dec_ref(v_post_1720_);
lean_dec_ref(v_pre_1719_);
v_val_1779_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1779_);
lean_dec_ref(v___x_1743_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_val_1779_);
v___x_1781_ = v___x_1741_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_val_1779_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1739_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1781_);
v___x_1783_ = v___x_1736_;
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
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_e_1724_);
lean_dec_ref(v_post_1720_);
lean_dec_ref(v_pre_1719_);
v_a_1788_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1733_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1733_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1796_, lean_object* v_pre_1797_, lean_object* v_post_1798_, lean_object* v_usedLetOnly_1799_, lean_object* v_skipConstInApp_1800_, lean_object* v_skipInstances_1801_, lean_object* v_body_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v_usedLetOnly_boxed_1811_; uint8_t v_skipConstInApp_boxed_1812_; uint8_t v_skipInstances_boxed_1813_; lean_object* v_res_1814_; 
v_usedLetOnly_boxed_1811_ = lean_unbox(v_usedLetOnly_1799_);
v_skipConstInApp_boxed_1812_ = lean_unbox(v_skipConstInApp_1800_);
v_skipInstances_boxed_1813_ = lean_unbox(v_skipInstances_1801_);
v_res_1814_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_1796_, v_pre_1797_, v_post_1798_, v_usedLetOnly_boxed_1811_, v_skipConstInApp_boxed_1812_, v_skipInstances_boxed_1813_, v_body_1802_, v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1804_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_pre_1815_, lean_object* v_post_1816_, uint8_t v_usedLetOnly_1817_, uint8_t v_skipConstInApp_1818_, uint8_t v_skipInstances_1819_, lean_object* v_fvars_1820_, lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
if (lean_obj_tag(v_e_1821_) == 7)
{
lean_object* v_binderName_1829_; lean_object* v_binderType_1830_; lean_object* v_body_1831_; uint8_t v_binderInfo_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_binderName_1829_ = lean_ctor_get(v_e_1821_, 0);
lean_inc(v_binderName_1829_);
v_binderType_1830_ = lean_ctor_get(v_e_1821_, 1);
lean_inc_ref(v_binderType_1830_);
v_body_1831_ = lean_ctor_get(v_e_1821_, 2);
lean_inc_ref(v_body_1831_);
v_binderInfo_1832_ = lean_ctor_get_uint8(v_e_1821_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1821_);
v___x_1833_ = lean_expr_instantiate_rev(v_binderType_1830_, v_fvars_1820_);
lean_dec_ref(v_binderType_1830_);
lean_inc_ref(v_post_1816_);
lean_inc_ref(v_pre_1815_);
v___x_1834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1815_, v_post_1816_, v_usedLetOnly_1817_, v_skipConstInApp_1818_, v_skipInstances_1819_, v___x_1833_, v_a_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_fst_1836_; lean_object* v_snd_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1834_);
v_fst_1836_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_fst_1836_);
v_snd_1837_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1837_);
lean_dec(v_a_1835_);
v___x_1838_ = lean_box(v_usedLetOnly_1817_);
v___x_1839_ = lean_box(v_skipConstInApp_1818_);
v___x_1840_ = lean_box(v_skipInstances_1819_);
v___f_1841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1841_, 0, v_fvars_1820_);
lean_closure_set(v___f_1841_, 1, v_pre_1815_);
lean_closure_set(v___f_1841_, 2, v_post_1816_);
lean_closure_set(v___f_1841_, 3, v___x_1838_);
lean_closure_set(v___f_1841_, 4, v___x_1839_);
lean_closure_set(v___f_1841_, 5, v___x_1840_);
lean_closure_set(v___f_1841_, 6, v_body_1831_);
v___x_1842_ = 0;
v___x_1843_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_1829_, v_binderInfo_1832_, v_fst_1836_, v___f_1841_, v___x_1842_, v_a_1822_, v_snd_1837_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1843_;
}
else
{
lean_dec_ref(v_body_1831_);
lean_dec(v_binderName_1829_);
lean_dec_ref(v_fvars_1820_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_expr_instantiate_rev(v_e_1821_, v_fvars_1820_);
lean_dec_ref(v_e_1821_);
lean_inc_ref(v_post_1816_);
lean_inc_ref(v_pre_1815_);
v___x_1845_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1815_, v_post_1816_, v_usedLetOnly_1817_, v_skipConstInApp_1818_, v_skipInstances_1819_, v___x_1844_, v_a_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v_fst_1847_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_fst_1847_);
v_snd_1848_ = lean_ctor_get(v_a_1846_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1846_);
v___x_1849_ = 0;
v___x_1850_ = 1;
v___x_1851_ = 1;
v___x_1852_ = l_Lean_Meta_mkForallFVars(v_fvars_1820_, v_fst_1847_, v___x_1849_, v_usedLetOnly_1817_, v___x_1850_, v___x_1851_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec_ref(v_fvars_1820_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1815_, v_post_1816_, v_usedLetOnly_1817_, v_skipConstInApp_1818_, v_skipInstances_1819_, v_a_1853_, v_a_1822_, v_snd_1848_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1854_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_snd_1848_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
v_a_1855_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1852_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1852_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1820_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(lean_object* v_fvars_1863_, lean_object* v_pre_1864_, lean_object* v_post_1865_, uint8_t v_usedLetOnly_1866_, uint8_t v_skipConstInApp_1867_, uint8_t v_skipInstances_1868_, lean_object* v_body_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_array_push(v_fvars_1863_, v_x_1870_);
v___x_1879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1864_, v_post_1865_, v_usedLetOnly_1866_, v_skipConstInApp_1867_, v_skipInstances_1868_, v___x_1878_, v_body_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(lean_object* v_pre_1880_, lean_object* v_post_1881_, lean_object* v_usedLetOnly_1882_, lean_object* v_skipConstInApp_1883_, lean_object* v_skipInstances_1884_, lean_object* v_sz_1885_, lean_object* v_i_1886_, lean_object* v_bs_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v_usedLetOnly_boxed_1895_; uint8_t v_skipConstInApp_boxed_1896_; uint8_t v_skipInstances_boxed_1897_; size_t v_sz_boxed_1898_; size_t v_i_boxed_1899_; lean_object* v_res_1900_; 
v_usedLetOnly_boxed_1895_ = lean_unbox(v_usedLetOnly_1882_);
v_skipConstInApp_boxed_1896_ = lean_unbox(v_skipConstInApp_1883_);
v_skipInstances_boxed_1897_ = lean_unbox(v_skipInstances_1884_);
v_sz_boxed_1898_ = lean_unbox_usize(v_sz_1885_);
lean_dec(v_sz_1885_);
v_i_boxed_1899_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_1880_, v_post_1881_, v_usedLetOnly_boxed_1895_, v_skipConstInApp_boxed_1896_, v_skipInstances_boxed_1897_, v_sz_boxed_1898_, v_i_boxed_1899_, v_bs_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1888_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1901_, lean_object* v_post_1902_, lean_object* v_usedLetOnly_1903_, lean_object* v_skipConstInApp_1904_, lean_object* v_skipInstances_1905_, lean_object* v_e_1906_, lean_object* v_a_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v_usedLetOnly_boxed_1914_; uint8_t v_skipConstInApp_boxed_1915_; uint8_t v_skipInstances_boxed_1916_; lean_object* v_res_1917_; 
v_usedLetOnly_boxed_1914_ = lean_unbox(v_usedLetOnly_1903_);
v_skipConstInApp_boxed_1915_ = lean_unbox(v_skipConstInApp_1904_);
v_skipInstances_boxed_1916_ = lean_unbox(v_skipInstances_1905_);
v_res_1917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1901_, v_post_1902_, v_usedLetOnly_boxed_1914_, v_skipConstInApp_boxed_1915_, v_skipInstances_boxed_1916_, v_e_1906_, v_a_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v_a_1907_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_pre_1918_, lean_object* v_post_1919_, lean_object* v_usedLetOnly_1920_, lean_object* v_skipConstInApp_1921_, lean_object* v_skipInstances_1922_, lean_object* v_fvars_1923_, lean_object* v_e_1924_, lean_object* v_a_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_usedLetOnly_boxed_1932_; uint8_t v_skipConstInApp_boxed_1933_; uint8_t v_skipInstances_boxed_1934_; lean_object* v_res_1935_; 
v_usedLetOnly_boxed_1932_ = lean_unbox(v_usedLetOnly_1920_);
v_skipConstInApp_boxed_1933_ = lean_unbox(v_skipConstInApp_1921_);
v_skipInstances_boxed_1934_ = lean_unbox(v_skipInstances_1922_);
v_res_1935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_1918_, v_post_1919_, v_usedLetOnly_boxed_1932_, v_skipConstInApp_boxed_1933_, v_skipInstances_boxed_1934_, v_fvars_1923_, v_e_1924_, v_a_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_a_1925_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1936_, lean_object* v_post_1937_, lean_object* v_usedLetOnly_1938_, lean_object* v_skipConstInApp_1939_, lean_object* v_skipInstances_1940_, lean_object* v_fvars_1941_, lean_object* v_e_1942_, lean_object* v_a_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v_usedLetOnly_boxed_1950_; uint8_t v_skipConstInApp_boxed_1951_; uint8_t v_skipInstances_boxed_1952_; lean_object* v_res_1953_; 
v_usedLetOnly_boxed_1950_ = lean_unbox(v_usedLetOnly_1938_);
v_skipConstInApp_boxed_1951_ = lean_unbox(v_skipConstInApp_1939_);
v_skipInstances_boxed_1952_ = lean_unbox(v_skipInstances_1940_);
v_res_1953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1936_, v_post_1937_, v_usedLetOnly_boxed_1950_, v_skipConstInApp_boxed_1951_, v_skipInstances_boxed_1952_, v_fvars_1941_, v_e_1942_, v_a_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v_a_1943_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1954_, lean_object* v_post_1955_, lean_object* v_usedLetOnly_1956_, lean_object* v_skipConstInApp_1957_, lean_object* v_skipInstances_1958_, lean_object* v_e_1959_, lean_object* v_a_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_usedLetOnly_boxed_1967_; uint8_t v_skipConstInApp_boxed_1968_; uint8_t v_skipInstances_boxed_1969_; lean_object* v_res_1970_; 
v_usedLetOnly_boxed_1967_ = lean_unbox(v_usedLetOnly_1956_);
v_skipConstInApp_boxed_1968_ = lean_unbox(v_skipConstInApp_1957_);
v_skipInstances_boxed_1969_ = lean_unbox(v_skipInstances_1958_);
v_res_1970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1954_, v_post_1955_, v_usedLetOnly_boxed_1967_, v_skipConstInApp_boxed_1968_, v_skipInstances_boxed_1969_, v_e_1959_, v_a_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_a_1960_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1971_, lean_object* v_post_1972_, lean_object* v_usedLetOnly_1973_, lean_object* v_skipConstInApp_1974_, lean_object* v_skipInstances_1975_, lean_object* v_fvars_1976_, lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v_usedLetOnly_boxed_1985_; uint8_t v_skipConstInApp_boxed_1986_; uint8_t v_skipInstances_boxed_1987_; lean_object* v_res_1988_; 
v_usedLetOnly_boxed_1985_ = lean_unbox(v_usedLetOnly_1973_);
v_skipConstInApp_boxed_1986_ = lean_unbox(v_skipConstInApp_1974_);
v_skipInstances_boxed_1987_ = lean_unbox(v_skipInstances_1975_);
v_res_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1971_, v_post_1972_, v_usedLetOnly_boxed_1985_, v_skipConstInApp_boxed_1986_, v_skipInstances_boxed_1987_, v_fvars_1976_, v_e_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_a_1978_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_1989_, lean_object* v___x_1990_, lean_object* v_pre_1991_, lean_object* v_post_1992_, lean_object* v_usedLetOnly_1993_, lean_object* v_skipConstInApp_1994_, lean_object* v_skipInstances_1995_, lean_object* v_a_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_usedLetOnly_boxed_2005_; uint8_t v_skipConstInApp_boxed_2006_; uint8_t v_skipInstances_boxed_2007_; lean_object* v_res_2008_; 
v_usedLetOnly_boxed_2005_ = lean_unbox(v_usedLetOnly_1993_);
v_skipConstInApp_boxed_2006_ = lean_unbox(v_skipConstInApp_1994_);
v_skipInstances_boxed_2007_ = lean_unbox(v_skipInstances_1995_);
v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_1989_, v___x_1990_, v_pre_1991_, v_post_1992_, v_usedLetOnly_boxed_2005_, v_skipConstInApp_boxed_2006_, v_skipInstances_boxed_2007_, v_a_1996_, v_b_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1998_);
lean_dec_ref(v___x_1990_);
lean_dec(v_upperBound_1989_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_skipInstances_2009_, lean_object* v_pre_2010_, lean_object* v_post_2011_, lean_object* v_usedLetOnly_2012_, lean_object* v_skipConstInApp_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_skipInstances_boxed_2024_; uint8_t v_usedLetOnly_boxed_2025_; uint8_t v_skipConstInApp_boxed_2026_; lean_object* v_res_2027_; 
v_skipInstances_boxed_2024_ = lean_unbox(v_skipInstances_2009_);
v_usedLetOnly_boxed_2025_ = lean_unbox(v_usedLetOnly_2012_);
v_skipConstInApp_boxed_2026_ = lean_unbox(v_skipConstInApp_2013_);
v_res_2027_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_2024_, v_pre_2010_, v_post_2011_, v_usedLetOnly_boxed_2025_, v_skipConstInApp_boxed_2026_, v_x_2014_, v_x_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2017_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_apply_1(v_x_2029_, lean_box(0));
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v___y_2030_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2039_, v_x_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_unsigned_to_nat(16u);
v___x_2050_ = lean_mk_array(v___x_2049_, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2051_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2055_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2055_, 0, lean_box(0));
lean_closure_set(v___x_2055_, 1, lean_box(0));
lean_closure_set(v___x_2055_, 2, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2056_, lean_object* v_pre_2057_, lean_object* v_post_2058_, uint8_t v_usedLetOnly_2059_, uint8_t v_skipConstInApp_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_a_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2067_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2068_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2067_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
v_fst_2070_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v_a_2069_, 1);
lean_inc(v_snd_2071_);
lean_dec(v_a_2069_);
v___x_2072_ = 0;
v___x_2073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2057_, v_post_2058_, v_usedLetOnly_2059_, v_skipConstInApp_2060_, v___x_2072_, v_input_2056_, v_fst_2070_, v_snd_2071_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2095_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v_fst_2075_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_fst_2075_);
v_snd_2076_ = lean_ctor_get(v_a_2074_, 1);
lean_inc(v_snd_2076_);
lean_dec(v_a_2074_);
v___x_2077_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2077_, 0, lean_box(0));
lean_closure_set(v___x_2077_, 1, lean_box(0));
lean_closure_set(v___x_2077_, 2, v_fst_2070_);
v___x_2078_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2077_, v_snd_2076_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_snd_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2093_; 
v_snd_2083_ = lean_ctor_get(v_a_2079_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_2079_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_a_2079_, 0);
lean_dec(v_unused_2094_);
v___x_2085_ = v_a_2079_;
v_isShared_2086_ = v_isSharedCheck_2093_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_snd_2083_);
lean_dec(v_a_2079_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2093_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_fst_2075_);
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_fst_2075_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_snd_2083_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2088_);
v___x_2090_ = v___x_2081_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
else
{
lean_dec(v_fst_2070_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2096_, lean_object* v_pre_2097_, lean_object* v_post_2098_, lean_object* v_usedLetOnly_2099_, lean_object* v_skipConstInApp_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v_usedLetOnly_boxed_2107_; uint8_t v_skipConstInApp_boxed_2108_; lean_object* v_res_2109_; 
v_usedLetOnly_boxed_2107_ = lean_unbox(v_usedLetOnly_2099_);
v_skipConstInApp_boxed_2108_ = lean_unbox(v_skipConstInApp_2100_);
v_res_2109_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2096_, v_pre_2097_, v_post_2098_, v_usedLetOnly_boxed_2107_, v_skipConstInApp_boxed_2108_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2109_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2112_; uint64_t v___x_2113_; 
v___x_2112_ = 3;
v___x_2113_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; uint8_t v_foApprox_2121_; uint8_t v_ctxApprox_2122_; uint8_t v_quasiPatternApprox_2123_; uint8_t v_constApprox_2124_; uint8_t v_isDefEqStuckEx_2125_; uint8_t v_unificationHints_2126_; uint8_t v_proofIrrelevance_2127_; uint8_t v_assignSyntheticOpaque_2128_; uint8_t v_offsetCnstrs_2129_; uint8_t v_etaStruct_2130_; uint8_t v_univApprox_2131_; uint8_t v_iota_2132_; uint8_t v_beta_2133_; uint8_t v_proj_2134_; uint8_t v_zeta_2135_; uint8_t v_zetaDelta_2136_; uint8_t v_zetaUnused_2137_; uint8_t v_zetaHave_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2169_; 
v___x_2120_ = l_Lean_Meta_Context_config(v_a_2115_);
v_foApprox_2121_ = lean_ctor_get_uint8(v___x_2120_, 0);
v_ctxApprox_2122_ = lean_ctor_get_uint8(v___x_2120_, 1);
v_quasiPatternApprox_2123_ = lean_ctor_get_uint8(v___x_2120_, 2);
v_constApprox_2124_ = lean_ctor_get_uint8(v___x_2120_, 3);
v_isDefEqStuckEx_2125_ = lean_ctor_get_uint8(v___x_2120_, 4);
v_unificationHints_2126_ = lean_ctor_get_uint8(v___x_2120_, 5);
v_proofIrrelevance_2127_ = lean_ctor_get_uint8(v___x_2120_, 6);
v_assignSyntheticOpaque_2128_ = lean_ctor_get_uint8(v___x_2120_, 7);
v_offsetCnstrs_2129_ = lean_ctor_get_uint8(v___x_2120_, 8);
v_etaStruct_2130_ = lean_ctor_get_uint8(v___x_2120_, 10);
v_univApprox_2131_ = lean_ctor_get_uint8(v___x_2120_, 11);
v_iota_2132_ = lean_ctor_get_uint8(v___x_2120_, 12);
v_beta_2133_ = lean_ctor_get_uint8(v___x_2120_, 13);
v_proj_2134_ = lean_ctor_get_uint8(v___x_2120_, 14);
v_zeta_2135_ = lean_ctor_get_uint8(v___x_2120_, 15);
v_zetaDelta_2136_ = lean_ctor_get_uint8(v___x_2120_, 16);
v_zetaUnused_2137_ = lean_ctor_get_uint8(v___x_2120_, 17);
v_zetaHave_2138_ = lean_ctor_get_uint8(v___x_2120_, 18);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2140_ = v___x_2120_;
v_isShared_2141_ = v_isSharedCheck_2169_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v___x_2120_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2169_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
uint8_t v_trackZetaDelta_2142_; lean_object* v_zetaDeltaSet_2143_; lean_object* v_lctx_2144_; lean_object* v_localInstances_2145_; lean_object* v_defEqCtx_x3f_2146_; lean_object* v_synthPendingDepth_2147_; lean_object* v_canUnfold_x3f_2148_; uint8_t v_univApprox_2149_; uint8_t v_inTypeClassResolution_2150_; uint8_t v_cacheInferType_2151_; uint8_t v___x_2152_; lean_object* v_config_2154_; 
v_trackZetaDelta_2142_ = lean_ctor_get_uint8(v_a_2115_, sizeof(void*)*7);
v_zetaDeltaSet_2143_ = lean_ctor_get(v_a_2115_, 1);
v_lctx_2144_ = lean_ctor_get(v_a_2115_, 2);
v_localInstances_2145_ = lean_ctor_get(v_a_2115_, 3);
v_defEqCtx_x3f_2146_ = lean_ctor_get(v_a_2115_, 4);
v_synthPendingDepth_2147_ = lean_ctor_get(v_a_2115_, 5);
v_canUnfold_x3f_2148_ = lean_ctor_get(v_a_2115_, 6);
v_univApprox_2149_ = lean_ctor_get_uint8(v_a_2115_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2150_ = lean_ctor_get_uint8(v_a_2115_, sizeof(void*)*7 + 2);
v_cacheInferType_2151_ = lean_ctor_get_uint8(v_a_2115_, sizeof(void*)*7 + 3);
v___x_2152_ = 3;
if (v_isShared_2141_ == 0)
{
v_config_2154_ = v___x_2140_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 0, v_foApprox_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 1, v_ctxApprox_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 2, v_quasiPatternApprox_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 3, v_constApprox_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 4, v_isDefEqStuckEx_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 5, v_unificationHints_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 6, v_proofIrrelevance_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 7, v_assignSyntheticOpaque_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 8, v_offsetCnstrs_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 10, v_etaStruct_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 11, v_univApprox_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 12, v_iota_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 13, v_beta_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 14, v_proj_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 15, v_zeta_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 16, v_zetaDelta_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 17, v_zetaUnused_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2168_, 18, v_zetaHave_2138_);
v_config_2154_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; uint64_t v___x_2162_; uint64_t v___x_2163_; uint64_t v_key_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_ctor_set_uint8(v_config_2154_, 9, v___x_2152_);
v___x_2155_ = l_Lean_Meta_Context_configKey(v_a_2115_);
v___x_2156_ = 2ULL;
v___x_2157_ = lean_uint64_shift_right(v___x_2155_, v___x_2156_);
v___f_2158_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2159_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2160_ = 0;
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_uint64_shift_left(v___x_2157_, v___x_2156_);
v___x_2163_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2164_ = lean_uint64_lor(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2165_, 0, v_config_2154_);
lean_ctor_set_uint64(v___x_2165_, sizeof(void*)*1, v_key_2164_);
lean_inc(v_canUnfold_x3f_2148_);
lean_inc(v_synthPendingDepth_2147_);
lean_inc(v_defEqCtx_x3f_2146_);
lean_inc_ref(v_localInstances_2145_);
lean_inc_ref(v_lctx_2144_);
lean_inc(v_zetaDeltaSet_2143_);
v___x_2166_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v_zetaDeltaSet_2143_);
lean_ctor_set(v___x_2166_, 2, v_lctx_2144_);
lean_ctor_set(v___x_2166_, 3, v_localInstances_2145_);
lean_ctor_set(v___x_2166_, 4, v_defEqCtx_x3f_2146_);
lean_ctor_set(v___x_2166_, 5, v_synthPendingDepth_2147_);
lean_ctor_set(v___x_2166_, 6, v_canUnfold_x3f_2148_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*7, v_trackZetaDelta_2142_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*7 + 1, v_univApprox_2149_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2150_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*7 + 3, v_cacheInferType_2151_);
v___x_2167_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2114_, v___f_2159_, v___f_2158_, v___x_2160_, v___x_2160_, v___x_2161_, v___x_2166_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec_ref(v___x_2166_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Meta_expandCoe(v_e_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2177_, lean_object* v_m_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2178_, v_a_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2181_, lean_object* v_m_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2181_, v_m_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_m_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2186_, v_x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_res_2192_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2189_, v_x_2190_, v_x_2191_);
lean_dec_ref(v_x_2191_);
lean_dec_ref(v_x_2190_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2194_, lean_object* v_a_2195_, lean_object* v_x_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_2195_, v_x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2198_, lean_object* v_a_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_2198_, v_a_2199_, v_x_2200_);
lean_dec(v_x_2200_);
lean_dec(v_a_2199_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_upperBound_2202_, lean_object* v___x_2203_, lean_object* v_pre_2204_, lean_object* v_post_2205_, uint8_t v_usedLetOnly_2206_, uint8_t v_skipConstInApp_2207_, uint8_t v_skipInstances_2208_, lean_object* v___x_2209_, lean_object* v_inst_2210_, lean_object* v_R_2211_, lean_object* v_a_2212_, lean_object* v_b_2213_, lean_object* v_c_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_2202_, v___x_2203_, v_pre_2204_, v_post_2205_, v_usedLetOnly_2206_, v_skipConstInApp_2207_, v_skipInstances_2208_, v_a_2212_, v_b_2213_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object** _args){
lean_object* v_upperBound_2223_ = _args[0];
lean_object* v___x_2224_ = _args[1];
lean_object* v_pre_2225_ = _args[2];
lean_object* v_post_2226_ = _args[3];
lean_object* v_usedLetOnly_2227_ = _args[4];
lean_object* v_skipConstInApp_2228_ = _args[5];
lean_object* v_skipInstances_2229_ = _args[6];
lean_object* v___x_2230_ = _args[7];
lean_object* v_inst_2231_ = _args[8];
lean_object* v_R_2232_ = _args[9];
lean_object* v_a_2233_ = _args[10];
lean_object* v_b_2234_ = _args[11];
lean_object* v_c_2235_ = _args[12];
lean_object* v___y_2236_ = _args[13];
lean_object* v___y_2237_ = _args[14];
lean_object* v___y_2238_ = _args[15];
lean_object* v___y_2239_ = _args[16];
lean_object* v___y_2240_ = _args[17];
lean_object* v___y_2241_ = _args[18];
lean_object* v___y_2242_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2243_; uint8_t v_skipConstInApp_boxed_2244_; uint8_t v_skipInstances_boxed_2245_; lean_object* v_res_2246_; 
v_usedLetOnly_boxed_2243_ = lean_unbox(v_usedLetOnly_2227_);
v_skipConstInApp_boxed_2244_ = lean_unbox(v_skipConstInApp_2228_);
v_skipInstances_boxed_2245_ = lean_unbox(v_skipInstances_2229_);
v_res_2246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_2223_, v___x_2224_, v_pre_2225_, v_post_2226_, v_usedLetOnly_boxed_2243_, v_skipConstInApp_boxed_2244_, v_skipInstances_boxed_2245_, v___x_2230_, v_inst_2231_, v_R_2232_, v_a_2233_, v_b_2234_, v_c_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2236_);
lean_dec(v___x_2230_);
lean_dec_ref(v___x_2224_);
lean_dec(v_upperBound_2223_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_00_u03b2_2247_, lean_object* v_m_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_2248_, v_a_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object* v_00_u03b2_2251_, lean_object* v_m_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_2251_, v_m_2252_, v_a_2253_);
lean_dec_ref(v_a_2253_);
lean_dec_ref(v_m_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(lean_object* v_00_u03b1_2255_, lean_object* v_name_2256_, uint8_t v_bi_2257_, lean_object* v_type_2258_, lean_object* v_k_2259_, uint8_t v_kind_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_2256_, v_bi_2257_, v_type_2258_, v_k_2259_, v_kind_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_name_2270_, lean_object* v_bi_2271_, lean_object* v_type_2272_, lean_object* v_k_2273_, lean_object* v_kind_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_bi_boxed_2282_; uint8_t v_kind_boxed_2283_; lean_object* v_res_2284_; 
v_bi_boxed_2282_ = lean_unbox(v_bi_2271_);
v_kind_boxed_2283_ = lean_unbox(v_kind_2274_);
v_res_2284_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_2269_, v_name_2270_, v_bi_boxed_2282_, v_type_2272_, v_k_2273_, v_kind_boxed_2283_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2275_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, lean_object* v_type_2287_, lean_object* v_val_2288_, lean_object* v_k_2289_, uint8_t v_nondep_2290_, uint8_t v_kind_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_2286_, v_type_2287_, v_val_2288_, v_k_2289_, v_nondep_2290_, v_kind_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_name_2301_, lean_object* v_type_2302_, lean_object* v_val_2303_, lean_object* v_k_2304_, lean_object* v_nondep_2305_, lean_object* v_kind_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v_nondep_boxed_2314_; uint8_t v_kind_boxed_2315_; lean_object* v_res_2316_; 
v_nondep_boxed_2314_ = lean_unbox(v_nondep_2305_);
v_kind_boxed_2315_ = lean_unbox(v_kind_2306_);
v_res_2316_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_2300_, v_name_2301_, v_type_2302_, v_val_2303_, v_k_2304_, v_nondep_boxed_2314_, v_kind_boxed_2315_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2307_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(lean_object* v_00_u03b1_2317_, lean_object* v_ref_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_2318_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b1_2325_, lean_object* v_ref_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_2325_, v_ref_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(lean_object* v_00_u03b1_2333_, lean_object* v_x_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_00_u03b1_2343_, lean_object* v_x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_2343_, v_x_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b2_2353_, lean_object* v_m_2354_, lean_object* v_a_2355_, lean_object* v_b_2356_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_2354_, v_a_2355_, v_b_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2358_, lean_object* v_x_2359_, size_t v_x_2360_, lean_object* v_x_2361_){
_start:
{
uint8_t v___x_2362_; 
v___x_2362_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2359_, v_x_2360_, v_x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_){
_start:
{
size_t v_x_39387__boxed_2367_; uint8_t v_res_2368_; lean_object* v_r_2369_; 
v_x_39387__boxed_2367_ = lean_unbox_usize(v_x_2365_);
lean_dec(v_x_2365_);
v_res_2368_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2363_, v_x_2364_, v_x_39387__boxed_2367_, v_x_2366_);
lean_dec_ref(v_x_2366_);
lean_dec_ref(v_x_2364_);
v_r_2369_ = lean_box(v_res_2368_);
return v_r_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(lean_object* v_00_u03b2_2370_, lean_object* v_a_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_2371_, v_x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(lean_object* v_00_u03b2_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_2374_, v_a_2375_, v_x_2376_);
lean_dec(v_x_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(lean_object* v_00_u03b2_2378_, lean_object* v_a_2379_, lean_object* v_x_2380_){
_start:
{
uint8_t v___x_2381_; 
v___x_2381_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_2379_, v_x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(lean_object* v_00_u03b2_2382_, lean_object* v_a_2383_, lean_object* v_x_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_2382_, v_a_2383_, v_x_2384_);
lean_dec(v_x_2384_);
lean_dec_ref(v_a_2383_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(lean_object* v_00_u03b2_2387_, lean_object* v_data_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(lean_object* v_00_u03b2_2390_, lean_object* v_a_2391_, lean_object* v_b_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_2391_, v_b_2392_, v_x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2395_, lean_object* v_keys_2396_, lean_object* v_vals_2397_, lean_object* v_heq_2398_, lean_object* v_i_2399_, lean_object* v_k_2400_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2396_, v_i_2399_, v_k_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2402_, lean_object* v_keys_2403_, lean_object* v_vals_2404_, lean_object* v_heq_2405_, lean_object* v_i_2406_, lean_object* v_k_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2402_, v_keys_2403_, v_vals_2404_, v_heq_2405_, v_i_2406_, v_k_2407_);
lean_dec_ref(v_k_2407_);
lean_dec_ref(v_vals_2404_);
lean_dec_ref(v_keys_2403_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(lean_object* v_00_u03b2_2410_, lean_object* v_i_2411_, lean_object* v_source_2412_, lean_object* v_target_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_2411_, v_source_2412_, v_target_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(lean_object* v_00_u03b2_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_2416_, v_x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2419_, lean_object* v_decl_2420_, lean_object* v_ref_2421_){
_start:
{
lean_object* v_defValue_2423_; lean_object* v_descr_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2451_; 
v_defValue_2423_ = lean_ctor_get(v_decl_2420_, 0);
v_descr_2424_ = lean_ctor_get(v_decl_2420_, 1);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_decl_2420_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2426_ = v_decl_2420_;
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_descr_2424_);
lean_inc(v_defValue_2423_);
lean_dec(v_decl_2420_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2451_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = lean_alloc_ctor(1, 0, 1);
v___x_2429_ = lean_unbox(v_defValue_2423_);
lean_ctor_set_uint8(v___x_2428_, 0, v___x_2429_);
lean_inc_n(v_name_2419_, 2);
v___x_2430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2430_, 0, v_name_2419_);
lean_ctor_set(v___x_2430_, 1, v_ref_2421_);
lean_ctor_set(v___x_2430_, 2, v___x_2428_);
lean_ctor_set(v___x_2430_, 3, v_descr_2424_);
v___x_2431_ = lean_register_option(v_name_2419_, v___x_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2441_; 
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2431_, 0);
lean_dec(v_unused_2442_);
v___x_2433_ = v___x_2431_;
v_isShared_2434_ = v_isSharedCheck_2441_;
goto v_resetjp_2432_;
}
else
{
lean_dec(v___x_2431_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2441_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v_defValue_2423_);
lean_ctor_set(v___x_2426_, 0, v_name_2419_);
v___x_2436_ = v___x_2426_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_name_2419_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_defValue_2423_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2436_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_del_object(v___x_2426_);
lean_dec(v_defValue_2423_);
lean_dec(v_name_2419_);
v_a_2443_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2431_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2431_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2452_, lean_object* v_decl_2453_, lean_object* v_ref_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2452_, v_decl_2453_, v_ref_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2470_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2471_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2472_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2473_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2470_, v___x_2471_, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_ref_2482_; lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2492_; 
v_ref_2482_ = lean_ctor_get(v___y_2479_, 5);
v___x_2483_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2492_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2492_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_inc(v_ref_2482_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_ref_2482_);
lean_ctor_set(v___x_2488_, 1, v_a_2484_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 1);
lean_ctor_set(v___x_2486_, 0, v___x_2488_);
v___x_2490_ = v___x_2486_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2511_ = l_Lean_stringToMessageData(v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2515_, lean_object* v_expectedType_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___x_2522_; 
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc_ref(v_expr_2515_);
v___x_2522_ = lean_infer_type(v_expr_2515_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_n(v_a_2523_, 2);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l_Lean_Meta_getLevel(v_a_2523_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
lean_inc_ref(v_expectedType_2516_);
v___x_2526_ = l_Lean_Meta_getLevel(v_expectedType_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref(v___x_2526_);
v___x_2528_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_a_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_a_2525_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
lean_inc_ref(v___x_2531_);
v___x_2532_ = l_Lean_mkConst(v___x_2528_, v___x_2531_);
v___x_2533_ = lean_unsigned_to_nat(3u);
v___x_2534_ = lean_mk_empty_array_with_capacity(v___x_2533_);
lean_inc(v_a_2523_);
v___x_2535_ = lean_array_push(v___x_2534_, v_a_2523_);
lean_inc_ref(v_expr_2515_);
v___x_2536_ = lean_array_push(v___x_2535_, v_expr_2515_);
lean_inc_ref(v_expectedType_2516_);
v___x_2537_ = lean_array_push(v___x_2536_, v_expectedType_2516_);
v___x_2538_ = l_Lean_mkAppN(v___x_2532_, v___x_2537_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = lean_box(0);
v___x_2540_ = l_Lean_Meta_trySynthInstance(v___x_2538_, v___x_2539_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2638_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2638_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2638_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
switch(lean_obj_tag(v_a_2541_))
{
case 0:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec_ref(v___x_2531_);
lean_dec(v_a_2523_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v___x_2545_ = lean_box(0);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
case 1:
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2633_; 
lean_del_object(v___x_2543_);
v_a_2549_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2551_ = v_a_2541_;
v_isShared_2552_ = v_isSharedCheck_2633_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v_a_2541_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2633_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2553_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2554_ = l_Lean_mkConst(v___x_2553_, v___x_2531_);
v___x_2555_ = lean_unsigned_to_nat(4u);
v___x_2556_ = lean_mk_empty_array_with_capacity(v___x_2555_);
v___x_2557_ = lean_array_push(v___x_2556_, v_a_2523_);
lean_inc_ref(v_expr_2515_);
v___x_2558_ = lean_array_push(v___x_2557_, v_expr_2515_);
lean_inc_ref(v_expectedType_2516_);
v___x_2559_ = lean_array_push(v___x_2558_, v_expectedType_2516_);
v___x_2560_ = lean_array_push(v___x_2559_, v_a_2549_);
v___x_2561_ = l_Lean_mkAppN(v___x_2554_, v___x_2560_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = l_Lean_Meta_expandCoe(v___x_2561_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2624_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2624_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2624_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fst_2574_; lean_object* v___x_2575_; 
v_fst_2574_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_fst_2574_);
v___x_2575_ = lean_infer_type(v_fst_2574_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2575_);
lean_inc_ref(v_expectedType_2516_);
v___x_2577_ = l_Lean_Meta_isExprDefEq(v_a_2576_, v_expectedType_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; uint8_t v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = lean_unbox(v_a_2578_);
lean_dec(v_a_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2605_; 
lean_inc(v_fst_2574_);
lean_del_object(v___x_2565_);
lean_del_object(v___x_2551_);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_a_2563_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; lean_object* v_unused_2607_; 
v_unused_2606_ = lean_ctor_get(v_a_2563_, 1);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v_a_2563_, 0);
lean_dec(v_unused_2607_);
v___x_2581_ = v_a_2563_;
v_isShared_2582_ = v_isSharedCheck_2605_;
goto v_resetjp_2580_;
}
else
{
lean_dec(v_a_2563_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2605_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2584_ = l_Lean_indentExpr(v_expr_2515_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 7);
lean_ctor_set(v___x_2581_, 1, v___x_2584_);
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2586_ = v___x_2581_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v___x_2587_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_indentExpr(v_expectedType_2516_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_indentExpr(v_fst_2574_);
v___x_2594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2594_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
goto v___jp_2567_;
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2565_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2551_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2608_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2577_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2577_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_del_object(v___x_2565_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2551_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2616_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2575_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2575_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
v___jp_2567_:
{
lean_object* v___x_2569_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_a_2563_);
v___x_2569_ = v___x_2551_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2563_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2571_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2571_ = v___x_2565_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_del_object(v___x_2551_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2625_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2562_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2562_);
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
}
default: 
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
lean_dec_ref(v___x_2531_);
lean_dec(v_a_2523_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v___x_2634_ = lean_box(2);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2634_);
v___x_2636_ = v___x_2543_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v___x_2531_);
lean_dec(v_a_2523_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2639_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2540_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2540_);
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
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_a_2525_);
lean_dec(v_a_2523_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2647_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2526_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2526_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_a_2523_);
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2655_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2524_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2524_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_expectedType_2516_);
lean_dec_ref(v_expr_2515_);
v_a_2663_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2522_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2522_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2671_, lean_object* v_expectedType_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2671_, v_expectedType_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2679_, lean_object* v_msg_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2687_, v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2695_, lean_object* v_expectedType_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2695_, v_expectedType_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2727_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2727_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2727_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
switch(lean_obj_tag(v_a_2703_))
{
case 0:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_box(0);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2707_);
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
case 1:
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2722_; 
v_a_2711_ = lean_ctor_get(v_a_2703_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2713_ = v_a_2703_;
v_isShared_2714_ = v_isSharedCheck_2722_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v_a_2703_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2722_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_fst_2715_; lean_object* v___x_2717_; 
v_fst_2715_ = lean_ctor_get(v_a_2711_, 0);
lean_inc(v_fst_2715_);
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_fst_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_fst_2715_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2717_);
v___x_2719_ = v___x_2705_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
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
default: 
{
lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2723_ = lean_box(2);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2723_);
v___x_2725_ = v___x_2705_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2702_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2702_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2736_, lean_object* v_expectedType_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2736_, v_expectedType_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2743_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; 
lean_inc(v_a_2763_);
lean_inc_ref(v_a_2762_);
lean_inc(v_a_2761_);
lean_inc_ref(v_a_2760_);
lean_inc_ref(v_expr_2759_);
v___x_2765_ = lean_infer_type(v_expr_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc_n(v_a_2766_, 2);
lean_dec_ref(v___x_2765_);
v___x_2767_ = l_Lean_Meta_getLevel(v_a_2766_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_n(v_a_2770_, 2);
lean_dec_ref(v___x_2769_);
v___x_2771_ = l_Lean_mkSort(v_a_2770_);
lean_inc(v_a_2766_);
v___x_2772_ = l_Lean_mkArrow(v_a_2766_, v___x_2771_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2772_);
v___x_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2774_, 0, v_a_2773_);
v___x_2775_ = 0;
v___x_2776_ = lean_box(0);
v___x_2777_ = l_Lean_Meta_mkFreshExprMVar(v___x_2774_, v___x_2775_, v___x_2776_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_n(v_a_2778_, 2);
lean_dec_ref(v___x_2777_);
v___x_2779_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2770_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_a_2768_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
lean_inc_ref(v___x_2782_);
v___x_2783_ = l_Lean_Expr_const___override(v___x_2779_, v___x_2782_);
lean_inc(v_a_2766_);
v___x_2784_ = l_Lean_mkAppB(v___x_2783_, v_a_2766_, v_a_2778_);
v___x_2785_ = lean_box(0);
v___x_2786_ = l_Lean_Meta_trySynthInstance(v___x_2784_, v___x_2785_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2873_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2873_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2873_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
if (lean_obj_tag(v_a_2787_) == 1)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2869_; 
lean_del_object(v___x_2789_);
v_a_2791_ = lean_ctor_get(v_a_2787_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2793_ = v_a_2787_;
v_isShared_2794_ = v_isSharedCheck_2869_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v_a_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2869_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2795_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2796_ = l_Lean_Expr_const___override(v___x_2795_, v___x_2782_);
lean_inc_ref(v_expr_2759_);
lean_inc(v_a_2791_);
v___x_2797_ = l_Lean_mkApp4(v___x_2796_, v_a_2766_, v_a_2778_, v_a_2791_, v_expr_2759_);
v___x_2798_ = l_Lean_Meta_expandCoe(v___x_2797_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2860_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2860_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2860_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_fst_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2858_; 
v_fst_2803_ = lean_ctor_get(v_a_2799_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_a_2799_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v_a_2799_, 1);
lean_dec(v_unused_2859_);
v___x_2805_ = v_a_2799_;
v_isShared_2806_ = v_isSharedCheck_2858_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_fst_2803_);
lean_dec(v_a_2799_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2858_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2814_; 
lean_inc(v_a_2763_);
lean_inc_ref(v_a_2762_);
lean_inc(v_a_2761_);
lean_inc_ref(v_a_2760_);
lean_inc(v_fst_2803_);
v___x_2814_ = lean_infer_type(v_fst_2803_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
lean_inc(v_a_2763_);
lean_inc_ref(v_a_2762_);
lean_inc(v_a_2761_);
lean_inc_ref(v_a_2760_);
v___x_2816_ = lean_whnf(v_a_2815_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; uint8_t v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = l_Lean_Expr_isForall(v_a_2817_);
lean_dec(v_a_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_del_object(v___x_2801_);
lean_del_object(v___x_2793_);
v___x_2819_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2820_ = l_Lean_indentExpr(v_expr_2759_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 7);
lean_ctor_set(v___x_2805_, 1, v___x_2820_);
lean_ctor_set(v___x_2805_, 0, v___x_2819_);
v___x_2822_ = v___x_2805_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v___x_2823_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_indentExpr(v_fst_2803_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2828_ = l_Lean_indentExpr(v_a_2791_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = l_Lean_MessageData_hint_x27(v___x_2829_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2826_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2831_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_del_object(v___x_2805_);
lean_dec(v_a_2791_);
lean_dec_ref(v_expr_2759_);
goto v___jp_2807_;
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2805_);
lean_dec(v_fst_2803_);
lean_del_object(v___x_2801_);
lean_del_object(v___x_2793_);
lean_dec(v_a_2791_);
lean_dec_ref(v_expr_2759_);
v_a_2842_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2816_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2816_);
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
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_del_object(v___x_2805_);
lean_dec(v_fst_2803_);
lean_del_object(v___x_2801_);
lean_del_object(v___x_2793_);
lean_dec(v_a_2791_);
lean_dec_ref(v_expr_2759_);
v_a_2850_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2814_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2814_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
v___jp_2807_:
{
lean_object* v___x_2809_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_fst_2803_);
v___x_2809_ = v___x_2793_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_fst_2803_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2811_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2809_);
v___x_2811_ = v___x_2801_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
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
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_del_object(v___x_2793_);
lean_dec(v_a_2791_);
lean_dec_ref(v_expr_2759_);
v_a_2861_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2798_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2798_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_object* v___x_2871_; 
lean_dec(v_a_2787_);
lean_dec_ref(v___x_2782_);
lean_dec(v_a_2778_);
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2785_);
v___x_2871_ = v___x_2789_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2785_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v___x_2782_);
lean_dec(v_a_2778_);
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
v_a_2874_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2786_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2786_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_a_2770_);
lean_dec(v_a_2768_);
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
v_a_2882_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2777_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2777_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2770_);
lean_dec(v_a_2768_);
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
v_a_2890_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2772_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2772_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_a_2768_);
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
v_a_2898_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2769_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2769_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2766_);
lean_dec_ref(v_expr_2759_);
v_a_2906_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2767_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2767_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_expr_2759_);
v_a_2914_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2765_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2765_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2928_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2937_ = l_Lean_stringToMessageData(v___x_2936_);
return v___x_2937_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2940_ = l_Lean_stringToMessageData(v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2947_; 
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
lean_inc(v_a_2943_);
lean_inc_ref(v_a_2942_);
lean_inc_ref(v_expr_2941_);
v___x_2947_ = lean_infer_type(v_expr_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc_n(v_a_2948_, 2);
lean_dec_ref(v___x_2947_);
v___x_2949_ = l_Lean_Meta_getLevel(v_a_2948_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_n(v_a_2952_, 2);
lean_dec_ref(v___x_2951_);
v___x_2953_ = l_Lean_mkSort(v_a_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = 0;
v___x_2956_ = lean_box(0);
v___x_2957_ = l_Lean_Meta_mkFreshExprMVar(v___x_2954_, v___x_2955_, v___x_2956_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc_n(v_a_2958_, 2);
lean_dec_ref(v___x_2957_);
v___x_2959_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_a_2952_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_a_2950_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
lean_inc_ref(v___x_2962_);
v___x_2963_ = l_Lean_Expr_const___override(v___x_2959_, v___x_2962_);
lean_inc(v_a_2948_);
v___x_2964_ = l_Lean_mkAppB(v___x_2963_, v_a_2948_, v_a_2958_);
v___x_2965_ = lean_box(0);
v___x_2966_ = l_Lean_Meta_trySynthInstance(v___x_2964_, v___x_2965_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3053_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_3053_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3053_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
if (lean_obj_tag(v_a_2967_) == 1)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_2969_);
v_a_2971_ = lean_ctor_get(v_a_2967_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_2973_ = v_a_2967_;
v_isShared_2974_ = v_isSharedCheck_3049_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v_a_2967_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3049_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2975_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_2976_ = l_Lean_Expr_const___override(v___x_2975_, v___x_2962_);
lean_inc_ref(v_expr_2941_);
lean_inc(v_a_2971_);
v___x_2977_ = l_Lean_mkApp4(v___x_2976_, v_a_2948_, v_a_2958_, v_a_2971_, v_expr_2941_);
v___x_2978_ = l_Lean_Meta_expandCoe(v___x_2977_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3040_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_3040_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3040_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v_fst_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3038_; 
v_fst_2983_ = lean_ctor_get(v_a_2979_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_2979_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; 
v_unused_3039_ = lean_ctor_get(v_a_2979_, 1);
lean_dec(v_unused_3039_);
v___x_2985_ = v_a_2979_;
v_isShared_2986_ = v_isSharedCheck_3038_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_fst_2983_);
lean_dec(v_a_2979_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3038_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2994_; 
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
lean_inc(v_a_2943_);
lean_inc_ref(v_a_2942_);
lean_inc(v_fst_2983_);
v___x_2994_ = lean_infer_type(v_fst_2983_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
lean_inc(v_a_2945_);
lean_inc_ref(v_a_2944_);
lean_inc(v_a_2943_);
lean_inc_ref(v_a_2942_);
v___x_2996_ = lean_whnf(v_a_2995_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; uint8_t v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2996_);
v___x_2998_ = l_Lean_Expr_isSort(v_a_2997_);
lean_dec(v_a_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_del_object(v___x_2981_);
lean_del_object(v___x_2973_);
v___x_2999_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3000_ = l_Lean_indentExpr(v_expr_2941_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 7);
lean_ctor_set(v___x_2985_, 1, v___x_3000_);
lean_ctor_set(v___x_2985_, 0, v___x_2999_);
v___x_3002_ = v___x_2985_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v___x_3003_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = l_Lean_indentExpr(v_fst_2983_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3004_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3008_ = l_Lean_indentExpr(v_a_2971_);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Lean_MessageData_hint_x27(v___x_3009_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3006_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3011_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_del_object(v___x_2985_);
lean_dec(v_a_2971_);
lean_dec_ref(v_expr_2941_);
goto v___jp_2987_;
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_del_object(v___x_2985_);
lean_dec(v_fst_2983_);
lean_del_object(v___x_2981_);
lean_del_object(v___x_2973_);
lean_dec(v_a_2971_);
lean_dec_ref(v_expr_2941_);
v_a_3022_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2996_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2996_);
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
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_2985_);
lean_dec(v_fst_2983_);
lean_del_object(v___x_2981_);
lean_del_object(v___x_2973_);
lean_dec(v_a_2971_);
lean_dec_ref(v_expr_2941_);
v_a_3030_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2994_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2994_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
v___jp_2987_:
{
lean_object* v___x_2989_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v_fst_2983_);
v___x_2989_ = v___x_2973_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_fst_2983_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2989_);
v___x_2991_ = v___x_2981_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
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
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_del_object(v___x_2973_);
lean_dec(v_a_2971_);
lean_dec_ref(v_expr_2941_);
v_a_3041_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2978_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2978_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v___x_3051_; 
lean_dec(v_a_2967_);
lean_dec_ref(v___x_2962_);
lean_dec(v_a_2958_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2941_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2965_);
v___x_3051_ = v___x_2969_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_2965_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___x_2962_);
lean_dec(v_a_2958_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2941_);
v_a_3054_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2966_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2966_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_a_2952_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2941_);
v_a_3062_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2957_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2957_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2941_);
v_a_3070_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2951_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2951_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_2948_);
lean_dec_ref(v_expr_2941_);
v_a_3078_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2949_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2949_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_expr_2941_);
v_a_3086_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_2947_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_2947_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3101_, lean_object* v___y_3102_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = l_Lean_Expr_hasMVar(v_e_3101_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_e_3101_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v_mctx_3107_; lean_object* v___x_3108_; lean_object* v_fst_3109_; lean_object* v_snd_3110_; lean_object* v___x_3111_; lean_object* v_cache_3112_; lean_object* v_zetaDeltaFVarIds_3113_; lean_object* v_postponed_3114_; lean_object* v_diag_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3124_; 
v___x_3106_ = lean_st_ref_get(v___y_3102_);
v_mctx_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_ref(v_mctx_3107_);
lean_dec(v___x_3106_);
v___x_3108_ = l_Lean_instantiateMVarsCore(v_mctx_3107_, v_e_3101_);
v_fst_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_fst_3109_);
v_snd_3110_ = lean_ctor_get(v___x_3108_, 1);
lean_inc(v_snd_3110_);
lean_dec_ref(v___x_3108_);
v___x_3111_ = lean_st_ref_take(v___y_3102_);
v_cache_3112_ = lean_ctor_get(v___x_3111_, 1);
v_zetaDeltaFVarIds_3113_ = lean_ctor_get(v___x_3111_, 2);
v_postponed_3114_ = lean_ctor_get(v___x_3111_, 3);
v_diag_3115_ = lean_ctor_get(v___x_3111_, 4);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3111_, 0);
lean_dec(v_unused_3125_);
v___x_3117_ = v___x_3111_;
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_diag_3115_);
lean_inc(v_postponed_3114_);
lean_inc(v_zetaDeltaFVarIds_3113_);
lean_inc(v_cache_3112_);
lean_dec(v___x_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3124_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v_snd_3110_);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_snd_3110_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_cache_3112_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_zetaDeltaFVarIds_3113_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_postponed_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_diag_3115_);
v___x_3120_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_st_ref_set(v___y_3102_, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_fst_3109_);
return v___x_3122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3126_, v___y_3127_);
lean_dec(v___y_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3130_, v___y_3132_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
return v_res_3143_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3144_; uint64_t v___x_3145_; 
v___x_3144_ = 2;
v___x_3145_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3152_; uint8_t v_foApprox_3153_; uint8_t v_ctxApprox_3154_; uint8_t v_quasiPatternApprox_3155_; uint8_t v_constApprox_3156_; uint8_t v_isDefEqStuckEx_3157_; uint8_t v_unificationHints_3158_; uint8_t v_proofIrrelevance_3159_; uint8_t v_assignSyntheticOpaque_3160_; uint8_t v_offsetCnstrs_3161_; uint8_t v_etaStruct_3162_; uint8_t v_univApprox_3163_; uint8_t v_iota_3164_; uint8_t v_beta_3165_; uint8_t v_proj_3166_; uint8_t v_zeta_3167_; uint8_t v_zetaDelta_3168_; uint8_t v_zetaUnused_3169_; uint8_t v_zetaHave_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3235_; 
v___x_3152_ = l_Lean_Meta_Context_config(v_a_3147_);
v_foApprox_3153_ = lean_ctor_get_uint8(v___x_3152_, 0);
v_ctxApprox_3154_ = lean_ctor_get_uint8(v___x_3152_, 1);
v_quasiPatternApprox_3155_ = lean_ctor_get_uint8(v___x_3152_, 2);
v_constApprox_3156_ = lean_ctor_get_uint8(v___x_3152_, 3);
v_isDefEqStuckEx_3157_ = lean_ctor_get_uint8(v___x_3152_, 4);
v_unificationHints_3158_ = lean_ctor_get_uint8(v___x_3152_, 5);
v_proofIrrelevance_3159_ = lean_ctor_get_uint8(v___x_3152_, 6);
v_assignSyntheticOpaque_3160_ = lean_ctor_get_uint8(v___x_3152_, 7);
v_offsetCnstrs_3161_ = lean_ctor_get_uint8(v___x_3152_, 8);
v_etaStruct_3162_ = lean_ctor_get_uint8(v___x_3152_, 10);
v_univApprox_3163_ = lean_ctor_get_uint8(v___x_3152_, 11);
v_iota_3164_ = lean_ctor_get_uint8(v___x_3152_, 12);
v_beta_3165_ = lean_ctor_get_uint8(v___x_3152_, 13);
v_proj_3166_ = lean_ctor_get_uint8(v___x_3152_, 14);
v_zeta_3167_ = lean_ctor_get_uint8(v___x_3152_, 15);
v_zetaDelta_3168_ = lean_ctor_get_uint8(v___x_3152_, 16);
v_zetaUnused_3169_ = lean_ctor_get_uint8(v___x_3152_, 17);
v_zetaHave_3170_ = lean_ctor_get_uint8(v___x_3152_, 18);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3172_ = v___x_3152_;
v_isShared_3173_ = v_isSharedCheck_3235_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v___x_3152_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3235_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v_trackZetaDelta_3174_; lean_object* v_zetaDeltaSet_3175_; lean_object* v_lctx_3176_; lean_object* v_localInstances_3177_; lean_object* v_defEqCtx_x3f_3178_; lean_object* v_synthPendingDepth_3179_; lean_object* v_canUnfold_x3f_3180_; uint8_t v_univApprox_3181_; uint8_t v_inTypeClassResolution_3182_; uint8_t v_cacheInferType_3183_; uint8_t v___x_3184_; lean_object* v_config_3186_; 
v_trackZetaDelta_3174_ = lean_ctor_get_uint8(v_a_3147_, sizeof(void*)*7);
v_zetaDeltaSet_3175_ = lean_ctor_get(v_a_3147_, 1);
v_lctx_3176_ = lean_ctor_get(v_a_3147_, 2);
v_localInstances_3177_ = lean_ctor_get(v_a_3147_, 3);
v_defEqCtx_x3f_3178_ = lean_ctor_get(v_a_3147_, 4);
v_synthPendingDepth_3179_ = lean_ctor_get(v_a_3147_, 5);
v_canUnfold_x3f_3180_ = lean_ctor_get(v_a_3147_, 6);
v_univApprox_3181_ = lean_ctor_get_uint8(v_a_3147_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3182_ = lean_ctor_get_uint8(v_a_3147_, sizeof(void*)*7 + 2);
v_cacheInferType_3183_ = lean_ctor_get_uint8(v_a_3147_, sizeof(void*)*7 + 3);
v___x_3184_ = 2;
if (v_isShared_3173_ == 0)
{
v_config_3186_ = v___x_3172_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 0, v_foApprox_3153_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 1, v_ctxApprox_3154_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 2, v_quasiPatternApprox_3155_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 3, v_constApprox_3156_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 4, v_isDefEqStuckEx_3157_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 5, v_unificationHints_3158_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 6, v_proofIrrelevance_3159_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 7, v_assignSyntheticOpaque_3160_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 8, v_offsetCnstrs_3161_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 10, v_etaStruct_3162_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 11, v_univApprox_3163_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 12, v_iota_3164_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 13, v_beta_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 14, v_proj_3166_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 15, v_zeta_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 16, v_zetaDelta_3168_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 17, v_zetaUnused_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3234_, 18, v_zetaHave_3170_);
v_config_3186_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
uint64_t v___x_3187_; uint64_t v___x_3188_; uint64_t v___x_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v_key_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_ctor_set_uint8(v_config_3186_, 9, v___x_3184_);
v___x_3187_ = l_Lean_Meta_Context_configKey(v_a_3147_);
v___x_3188_ = 2ULL;
v___x_3189_ = lean_uint64_shift_right(v___x_3187_, v___x_3188_);
v___x_3190_ = lean_uint64_shift_left(v___x_3189_, v___x_3188_);
v___x_3191_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3192_ = lean_uint64_lor(v___x_3190_, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3193_, 0, v_config_3186_);
lean_ctor_set_uint64(v___x_3193_, sizeof(void*)*1, v_key_3192_);
lean_inc(v_canUnfold_x3f_3180_);
lean_inc(v_synthPendingDepth_3179_);
lean_inc(v_defEqCtx_x3f_3178_);
lean_inc_ref(v_localInstances_3177_);
lean_inc_ref(v_lctx_3176_);
lean_inc(v_zetaDeltaSet_3175_);
v___x_3194_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v_zetaDeltaSet_3175_);
lean_ctor_set(v___x_3194_, 2, v_lctx_3176_);
lean_ctor_set(v___x_3194_, 3, v_localInstances_3177_);
lean_ctor_set(v___x_3194_, 4, v_defEqCtx_x3f_3178_);
lean_ctor_set(v___x_3194_, 5, v_synthPendingDepth_3179_);
lean_ctor_set(v___x_3194_, 6, v_canUnfold_x3f_3180_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*7, v_trackZetaDelta_3174_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*7 + 1, v_univApprox_3181_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3182_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*7 + 3, v_cacheInferType_3183_);
lean_inc(v_a_3150_);
lean_inc_ref(v_a_3149_);
lean_inc(v_a_3148_);
v___x_3195_ = lean_whnf(v_type_3146_, v___x_3194_, v_a_3148_, v_a_3149_, v_a_3150_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3225_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3225_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3225_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
if (lean_obj_tag(v_a_3196_) == 5)
{
lean_object* v_fn_3200_; lean_object* v_arg_3201_; lean_object* v___x_3202_; lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3220_; 
lean_del_object(v___x_3198_);
v_fn_3200_ = lean_ctor_get(v_a_3196_, 0);
lean_inc_ref(v_fn_3200_);
v_arg_3201_ = lean_ctor_get(v_a_3196_, 1);
lean_inc_ref(v_arg_3201_);
lean_dec_ref(v_a_3196_);
v___x_3202_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3200_, v_a_3148_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3220_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3220_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3219_; 
v___x_3207_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3201_, v_a_3148_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3219_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3219_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_a_3203_);
lean_ctor_set(v___x_3212_, 1, v_a_3208_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set_tag(v___x_3205_, 1);
lean_ctor_set(v___x_3205_, 0, v___x_3212_);
v___x_3214_ = v___x_3205_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3214_);
v___x_3216_ = v___x_3210_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
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
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec(v_a_3196_);
v___x_3221_ = lean_box(0);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3221_);
v___x_3223_ = v___x_3198_;
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
v_a_3226_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3195_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3195_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Meta_isTypeApp_x3f(v_type_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Meta_isTypeApp_x3f(v_type_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3285_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3285_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3285_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
if (lean_obj_tag(v_a_3250_) == 1)
{
lean_object* v_val_3254_; lean_object* v_fst_3255_; lean_object* v___x_3256_; 
lean_del_object(v___x_3252_);
v_val_3254_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_val_3254_);
lean_dec_ref(v_a_3250_);
v_fst_3255_ = lean_ctor_get(v_val_3254_, 0);
lean_inc(v_fst_3255_);
lean_dec(v_val_3254_);
v___x_3256_ = l_Lean_Meta_isMonad_x3f(v_fst_3255_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3271_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3271_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3271_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
if (lean_obj_tag(v_a_3257_) == 0)
{
uint8_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3261_ = 0;
v___x_3262_ = lean_box(v___x_3261_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3262_);
v___x_3264_ = v___x_3259_;
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
else
{
uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
lean_dec_ref(v_a_3257_);
v___x_3266_ = 1;
v___x_3267_ = lean_box(v___x_3266_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3267_);
v___x_3269_ = v___x_3259_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_a_3272_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3256_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3256_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_a_3250_);
v___x_3280_ = 0;
v___x_3281_ = lean_box(v___x_3280_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3281_);
v___x_3283_ = v___x_3252_;
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
v_a_3286_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3249_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3249_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Meta_isMonadApp(v_type_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3300_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3301_, lean_object* v_opt_3302_){
_start:
{
lean_object* v_name_3303_; lean_object* v_defValue_3304_; lean_object* v_map_3305_; lean_object* v___x_3306_; 
v_name_3303_ = lean_ctor_get(v_opt_3302_, 0);
v_defValue_3304_ = lean_ctor_get(v_opt_3302_, 1);
v_map_3305_ = lean_ctor_get(v_opts_3301_, 0);
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3305_, v_name_3303_);
if (lean_obj_tag(v___x_3306_) == 0)
{
uint8_t v___x_3307_; 
v___x_3307_ = lean_unbox(v_defValue_3304_);
return v___x_3307_;
}
else
{
lean_object* v_val_3308_; 
v_val_3308_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3308_);
lean_dec_ref(v___x_3306_);
if (lean_obj_tag(v_val_3308_) == 1)
{
uint8_t v_v_3309_; 
v_v_3309_ = lean_ctor_get_uint8(v_val_3308_, 0);
lean_dec_ref(v_val_3308_);
return v_v_3309_;
}
else
{
uint8_t v___x_3310_; 
lean_dec(v_val_3308_);
v___x_3310_ = lean_unbox(v_defValue_3304_);
return v___x_3310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3311_, lean_object* v_opt_3312_){
_start:
{
uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_res_3313_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3311_, v_opt_3312_);
lean_dec_ref(v_opt_3312_);
lean_dec_ref(v_opts_3311_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_x_3325_);
return v_res_3331_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = l_Lean_mkBVar(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3354_, lean_object* v_expectedType_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___y_3362_; uint8_t v___y_3363_; lean_object* v_a_3368_; lean_object* v___y_3372_; lean_object* v___x_3382_; lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3786_; 
v___x_3382_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3355_, v_a_3357_);
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3786_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3786_;
goto v_resetjp_3384_;
}
v___jp_3361_:
{
if (v___y_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec_ref(v___y_3362_);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___y_3362_);
return v___x_3366_;
}
}
v___jp_3367_:
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Lean_Exception_isInterrupt(v_a_3368_);
if (v___x_3369_ == 0)
{
uint8_t v___x_3370_; 
lean_inc_ref(v_a_3368_);
v___x_3370_ = l_Lean_Exception_isRuntime(v_a_3368_);
v___y_3362_ = v_a_3368_;
v___y_3363_ = v___x_3370_;
goto v___jp_3361_;
}
else
{
v___y_3362_ = v_a_3368_;
v___y_3363_ = v___x_3369_;
goto v___jp_3361_;
}
}
v___jp_3371_:
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3381_; 
v_a_3373_ = lean_ctor_get(v___y_3372_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___y_3372_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3375_ = v___y_3372_;
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___y_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_a_3377_; lean_object* v___x_3379_; 
v_a_3377_ = lean_ctor_get(v_a_3373_, 0);
lean_inc(v_a_3377_);
lean_dec(v_a_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v_a_3377_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; 
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
lean_inc_ref(v_e_3354_);
v___x_3387_ = lean_infer_type(v_e_3354_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3777_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3388_, v_a_3357_);
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3777_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3777_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; 
lean_inc(v_a_3383_);
v___x_3394_ = l_Lean_Meta_isTypeApp_x3f(v_a_3383_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3768_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3768_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3768_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_a_3395_) == 1)
{
lean_object* v_val_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3763_; 
lean_del_object(v___x_3397_);
v_val_3399_ = lean_ctor_get(v_a_3395_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3401_ = v_a_3395_;
v_isShared_3402_ = v_isSharedCheck_3763_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_val_3399_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3763_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_fst_3403_; lean_object* v_snd_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3762_; 
v_fst_3403_ = lean_ctor_get(v_val_3399_, 0);
v_snd_3404_ = lean_ctor_get(v_val_3399_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_val_3399_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3406_ = v_val_3399_;
v_isShared_3407_ = v_isSharedCheck_3762_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_snd_3404_);
lean_inc(v_fst_3403_);
lean_dec(v_val_3399_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3762_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; 
lean_inc(v_a_3390_);
v___x_3408_ = l_Lean_Meta_isTypeApp_x3f(v_a_3390_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3753_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3753_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3753_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
if (lean_obj_tag(v_a_3409_) == 1)
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3411_);
v_val_3413_ = lean_ctor_get(v_a_3409_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3409_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3415_ = v_a_3409_;
v_isShared_3416_ = v_isSharedCheck_3748_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v_a_3409_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3748_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_fst_3417_; lean_object* v_snd_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3747_; 
v_fst_3417_ = lean_ctor_get(v_val_3413_, 0);
v_snd_3418_ = lean_ctor_get(v_val_3413_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_val_3413_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3420_ = v_val_3413_;
v_isShared_3421_ = v_isSharedCheck_3747_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_snd_3418_);
lean_inc(v_fst_3417_);
lean_dec(v_val_3413_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3747_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Meta_saveState___redArg(v_a_3357_, v_a_3359_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref(v___x_3422_);
lean_inc(v_fst_3403_);
lean_inc(v_fst_3417_);
v___x_3424_ = l_Lean_Meta_isExprDefEq(v_fst_3417_, v_fst_3403_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3730_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3730_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3730_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_unbox(v_a_3425_);
lean_dec(v_a_3425_);
if (v___x_3429_ == 0)
{
lean_object* v_options_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
lean_dec(v_a_3423_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3385_);
v_options_3430_ = lean_ctor_get(v_a_3358_, 2);
v___x_3431_ = l_Lean_Meta_autoLift;
v___x_3432_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3433_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3433_);
v___x_3435_ = v___x_3427_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
else
{
lean_object* v___x_3437_; 
lean_del_object(v___x_3427_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
lean_inc(v_fst_3417_);
v___x_3437_ = lean_infer_type(v_fst_3417_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
v___x_3439_ = lean_whnf(v_a_3438_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v___x_3439_);
if (lean_obj_tag(v_a_3440_) == 7)
{
lean_object* v_binderType_3441_; 
v_binderType_3441_ = lean_ctor_get(v_a_3440_, 1);
if (lean_obj_tag(v_binderType_3441_) == 3)
{
lean_object* v_body_3442_; 
v_body_3442_ = lean_ctor_get(v_a_3440_, 2);
if (lean_obj_tag(v_body_3442_) == 3)
{
lean_object* v_u_3443_; lean_object* v_u_3444_; lean_object* v___x_3445_; 
lean_inc_ref(v_body_3442_);
lean_inc_ref(v_binderType_3441_);
lean_dec_ref(v_a_3440_);
v_u_3443_ = lean_ctor_get(v_binderType_3441_, 0);
lean_inc(v_u_3443_);
lean_dec_ref(v_binderType_3441_);
v_u_3444_ = lean_ctor_get(v_body_3442_, 0);
lean_inc(v_u_3444_);
lean_dec_ref(v_body_3442_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
lean_inc(v_fst_3403_);
v___x_3445_ = lean_infer_type(v_fst_3403_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
v___x_3447_ = lean_whnf(v_a_3446_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref(v___x_3447_);
if (lean_obj_tag(v_a_3448_) == 7)
{
lean_object* v_binderType_3449_; 
v_binderType_3449_ = lean_ctor_get(v_a_3448_, 1);
if (lean_obj_tag(v_binderType_3449_) == 3)
{
lean_object* v_body_3450_; 
v_body_3450_ = lean_ctor_get(v_a_3448_, 2);
if (lean_obj_tag(v_body_3450_) == 3)
{
lean_object* v_u_3451_; lean_object* v_u_3452_; lean_object* v___x_3453_; 
lean_inc_ref(v_body_3450_);
lean_inc_ref(v_binderType_3449_);
lean_dec_ref(v_a_3448_);
v_u_3451_ = lean_ctor_get(v_binderType_3449_, 0);
lean_inc(v_u_3451_);
lean_dec_ref(v_binderType_3449_);
v_u_3452_ = lean_ctor_get(v_body_3450_, 0);
lean_inc(v_u_3452_);
lean_dec_ref(v_body_3450_);
v___x_3453_ = l_Lean_Meta_decLevel(v_u_3443_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = l_Lean_Meta_decLevel(v_u_3451_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref(v___x_3455_);
lean_inc(v_a_3454_);
v___x_3457_ = l_Lean_Meta_isLevelDefEq(v_a_3454_, v_a_3456_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3622_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3622_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3622_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_unbox(v_a_3458_);
lean_dec(v_a_3458_);
if (v___x_3462_ == 1)
{
lean_object* v___x_3463_; 
lean_del_object(v___x_3460_);
v___x_3463_ = l_Lean_Meta_decLevel(v_u_3444_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = l_Lean_Meta_decLevel(v_u_3452_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref(v___x_3465_);
v___x_3467_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3468_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set_tag(v___x_3420_, 1);
lean_ctor_set(v___x_3420_, 1, v___x_3468_);
lean_ctor_set(v___x_3420_, 0, v_a_3466_);
v___x_3470_ = v___x_3420_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3466_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 1);
lean_ctor_set(v___x_3406_, 1, v___x_3470_);
lean_ctor_set(v___x_3406_, 0, v_a_3464_);
v___x_3472_ = v___x_3406_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3464_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3473_, 0, v_a_3454_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_Expr_const___override(v___x_3467_, v___x_3473_);
v___x_3475_ = lean_unsigned_to_nat(2u);
v___x_3476_ = lean_mk_empty_array_with_capacity(v___x_3475_);
lean_inc(v_fst_3417_);
v___x_3477_ = lean_array_push(v___x_3476_, v_fst_3417_);
lean_inc(v_fst_3403_);
v___x_3478_ = lean_array_push(v___x_3477_, v_fst_3403_);
v___x_3479_ = l_Lean_mkAppN(v___x_3474_, v___x_3478_);
lean_dec_ref(v___x_3478_);
v___x_3480_ = lean_box(0);
v___x_3481_ = l_Lean_Meta_trySynthInstance(v___x_3479_, v___x_3480_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3612_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3612_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3612_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
if (lean_obj_tag(v_a_3482_) == 1)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
lean_del_object(v___x_3484_);
v_a_3486_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v_a_3482_);
lean_inc(v_snd_3418_);
v___x_3487_ = l_Lean_Meta_getDecLevel(v_snd_3418_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3487_);
v___x_3489_ = l_Lean_Meta_getDecLevel(v_a_3390_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
lean_inc(v_a_3383_);
v___x_3491_ = l_Lean_Meta_getDecLevel(v_a_3383_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v_a_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3468_);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_a_3490_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_a_3488_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
lean_inc_ref(v___x_3496_);
v___x_3497_ = l_Lean_mkConst(v___x_3493_, v___x_3496_);
v___x_3498_ = lean_unsigned_to_nat(5u);
v___x_3499_ = lean_mk_empty_array_with_capacity(v___x_3498_);
lean_inc(v_fst_3417_);
v___x_3500_ = lean_array_push(v___x_3499_, v_fst_3417_);
lean_inc(v_fst_3403_);
v___x_3501_ = lean_array_push(v___x_3500_, v_fst_3403_);
lean_inc(v_a_3486_);
v___x_3502_ = lean_array_push(v___x_3501_, v_a_3486_);
lean_inc(v_snd_3418_);
v___x_3503_ = lean_array_push(v___x_3502_, v_snd_3418_);
lean_inc_ref(v_e_3354_);
v___x_3504_ = lean_array_push(v___x_3503_, v_e_3354_);
v___x_3505_ = l_Lean_mkAppN(v___x_3497_, v___x_3504_);
lean_dec_ref(v___x_3504_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
lean_inc_ref(v___x_3505_);
v___x_3506_ = lean_infer_type(v___x_3505_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3508_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref(v___x_3506_);
lean_inc(v_a_3383_);
v___x_3508_ = l_Lean_Meta_isExprDefEq(v_a_3383_, v_a_3507_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3603_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3603_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3603_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_unbox(v_a_3509_);
lean_dec(v_a_3509_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_del_object(v___x_3511_);
lean_dec_ref(v___x_3505_);
lean_del_object(v___x_3415_);
lean_inc(v_fst_3403_);
v___x_3514_ = l_Lean_Meta_isMonad_x3f(v_fst_3403_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3595_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3595_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3595_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
if (lean_obj_tag(v_a_3515_) == 1)
{
lean_object* v_val_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3517_);
v_val_3519_ = lean_ctor_get(v_a_3515_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3521_ = v_a_3515_;
v_isShared_3522_ = v_isSharedCheck_3591_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_val_3519_);
lean_dec(v_a_3515_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3591_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; 
lean_inc(v_snd_3418_);
v___x_3523_ = l_Lean_Meta_getLevel(v_snd_3418_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3523_);
lean_inc(v_snd_3404_);
v___x_3525_ = l_Lean_Meta_getLevel(v_snd_3404_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3528_ = 0;
v___x_3529_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_a_3526_);
lean_ctor_set(v___x_3530_, 1, v___x_3468_);
v___x_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_a_3524_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_mkConst(v___x_3529_, v___x_3531_);
v___x_3533_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3534_ = lean_unsigned_to_nat(3u);
v___x_3535_ = lean_mk_empty_array_with_capacity(v___x_3534_);
lean_inc_n(v_snd_3418_, 2);
v___x_3536_ = lean_array_push(v___x_3535_, v_snd_3418_);
v___x_3537_ = lean_array_push(v___x_3536_, v___x_3533_);
lean_inc(v_snd_3404_);
v___x_3538_ = lean_array_push(v___x_3537_, v_snd_3404_);
v___x_3539_ = l_Lean_mkAppN(v___x_3532_, v___x_3538_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = l_Lean_mkForall(v___x_3527_, v___x_3528_, v_snd_3418_, v___x_3539_);
v___x_3541_ = l_Lean_Meta_trySynthInstance(v___x_3540_, v___x_3480_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3587_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3544_ = v___x_3541_;
v_isShared_3545_ = v_isSharedCheck_3587_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3587_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
if (lean_obj_tag(v_a_3542_) == 1)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_del_object(v___x_3544_);
v_a_3546_ = lean_ctor_get(v_a_3542_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v_a_3542_);
v___x_3547_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3548_ = l_Lean_mkConst(v___x_3547_, v___x_3496_);
v___x_3549_ = lean_unsigned_to_nat(8u);
v___x_3550_ = lean_mk_empty_array_with_capacity(v___x_3549_);
v___x_3551_ = lean_array_push(v___x_3550_, v_fst_3417_);
v___x_3552_ = lean_array_push(v___x_3551_, v_fst_3403_);
v___x_3553_ = lean_array_push(v___x_3552_, v_snd_3418_);
v___x_3554_ = lean_array_push(v___x_3553_, v_snd_3404_);
v___x_3555_ = lean_array_push(v___x_3554_, v_a_3486_);
v___x_3556_ = lean_array_push(v___x_3555_, v_a_3546_);
v___x_3557_ = lean_array_push(v___x_3556_, v_val_3519_);
v___x_3558_ = lean_array_push(v___x_3557_, v_e_3354_);
v___x_3559_ = l_Lean_mkAppN(v___x_3548_, v___x_3558_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = l_Lean_Meta_expandCoe(v___x_3559_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v_fst_3562_; lean_object* v___x_3563_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref(v___x_3560_);
v_fst_3562_ = lean_ctor_get(v_a_3561_, 0);
lean_inc_n(v_fst_3562_, 2);
lean_dec(v_a_3561_);
lean_inc(v_a_3359_);
lean_inc_ref(v_a_3358_);
lean_inc(v_a_3357_);
lean_inc_ref(v_a_3356_);
v___x_3563_ = lean_infer_type(v_fst_3562_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v___x_3563_);
v___x_3565_ = l_Lean_Meta_isExprDefEq(v_a_3383_, v_a_3564_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3580_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3568_ = v___x_3565_;
v_isShared_3569_ = v_isSharedCheck_3580_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3565_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3580_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_unbox(v_a_3566_);
lean_dec(v_a_3566_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_fst_3562_);
lean_del_object(v___x_3521_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 0, v___x_3480_);
v___x_3572_ = v___x_3568_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3480_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
else
{
lean_object* v___x_3575_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v_fst_3562_);
v___x_3575_ = v___x_3521_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_fst_3562_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 0, v___x_3575_);
v___x_3577_ = v___x_3568_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
else
{
lean_object* v_a_3581_; 
lean_dec(v_fst_3562_);
lean_del_object(v___x_3521_);
v_a_3581_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3565_);
v_a_3368_ = v_a_3581_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3582_; 
lean_dec(v_fst_3562_);
lean_del_object(v___x_3521_);
lean_dec(v_a_3383_);
v_a_3582_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3582_);
lean_dec_ref(v___x_3563_);
v_a_3368_ = v_a_3582_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3583_; 
lean_del_object(v___x_3521_);
lean_dec(v_a_3383_);
v_a_3583_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3583_);
lean_dec_ref(v___x_3560_);
v_a_3368_ = v_a_3583_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3585_; 
lean_dec(v_a_3542_);
lean_del_object(v___x_3521_);
lean_dec(v_val_3519_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3480_);
v___x_3585_ = v___x_3544_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3480_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; 
lean_del_object(v___x_3521_);
lean_dec(v_val_3519_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3588_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3588_);
lean_dec_ref(v___x_3541_);
v_a_3368_ = v_a_3588_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3589_; 
lean_dec(v_a_3524_);
lean_del_object(v___x_3521_);
lean_dec(v_val_3519_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3589_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3525_);
v_a_3368_ = v_a_3589_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3590_; 
lean_del_object(v___x_3521_);
lean_dec(v_val_3519_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3590_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3590_);
lean_dec_ref(v___x_3523_);
v_a_3368_ = v_a_3590_;
goto v___jp_3367_;
}
}
}
else
{
lean_object* v___x_3593_; 
lean_dec(v_a_3515_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3480_);
v___x_3593_ = v___x_3517_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3480_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_a_3596_; 
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3596_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3514_);
v_a_3368_ = v_a_3596_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3598_; 
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3505_);
v___x_3598_ = v___x_3415_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3505_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3598_);
v___x_3600_ = v___x_3511_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
else
{
lean_object* v_a_3604_; 
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3604_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3508_);
v_a_3368_ = v_a_3604_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3605_; 
lean_dec_ref(v___x_3505_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3605_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3506_);
v_a_3368_ = v_a_3605_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3606_; 
lean_dec(v_a_3490_);
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3606_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3491_);
v_a_3368_ = v_a_3606_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3607_; 
lean_dec(v_a_3488_);
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3607_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3489_);
v_a_3368_ = v_a_3607_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3608_; 
lean_dec(v_a_3486_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3608_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3487_);
v_a_3368_ = v_a_3608_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_a_3482_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3480_);
v___x_3610_ = v___x_3484_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3480_);
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
else
{
lean_object* v_a_3613_; 
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3613_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3481_);
v_a_3368_ = v_a_3613_;
goto v___jp_3367_;
}
}
}
}
else
{
lean_object* v_a_3616_; 
lean_dec(v_a_3464_);
lean_dec(v_a_3454_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3616_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3616_);
lean_dec_ref(v___x_3465_);
v_a_3368_ = v_a_3616_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3617_; 
lean_dec(v_a_3454_);
lean_dec(v_u_3452_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3617_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3463_);
v_a_3368_ = v_a_3617_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_dec(v_a_3454_);
lean_dec(v_u_3452_);
lean_dec(v_u_3444_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3618_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3618_);
v___x_3620_ = v___x_3460_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
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
lean_dec(v_a_3454_);
lean_dec(v_u_3452_);
lean_dec(v_u_3444_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3623_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3457_);
v_a_3368_ = v_a_3623_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3624_; 
lean_dec(v_a_3454_);
lean_dec(v_u_3452_);
lean_dec(v_u_3444_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3624_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3455_);
v_a_3368_ = v_a_3624_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3625_; 
lean_dec(v_u_3452_);
lean_dec(v_u_3451_);
lean_dec(v_u_3444_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3625_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3453_);
v_a_3368_ = v_a_3625_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3626_; 
lean_dec(v_u_3444_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3626_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3448_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec_ref(v_a_3448_);
v___y_3372_ = v___x_3626_;
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3627_; 
lean_dec(v_u_3444_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3627_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3448_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec_ref(v_a_3448_);
v___y_3372_ = v___x_3627_;
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3628_; 
lean_dec(v_u_3444_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3628_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3448_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3448_);
v___y_3372_ = v___x_3628_;
goto v___jp_3371_;
}
}
else
{
lean_object* v_a_3629_; 
lean_dec(v_u_3444_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3629_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3447_);
v_a_3368_ = v_a_3629_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3630_; 
lean_dec(v_u_3444_);
lean_dec(v_u_3443_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3630_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3445_);
v_a_3368_ = v_a_3630_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3631_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3631_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3440_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec_ref(v_a_3440_);
v___y_3372_ = v___x_3631_;
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3632_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3632_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3440_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec_ref(v_a_3440_);
v___y_3372_ = v___x_3632_;
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3633_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3633_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3440_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3440_);
v___y_3372_ = v___x_3633_;
goto v___jp_3371_;
}
}
else
{
lean_object* v_a_3634_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3634_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3439_);
v_a_3368_ = v_a_3634_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3635_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3635_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3635_);
lean_dec_ref(v___x_3437_);
v_a_3368_ = v_a_3635_;
goto v___jp_3367_;
}
}
}
else
{
lean_object* v___x_3636_; 
lean_del_object(v___x_3427_);
lean_del_object(v___x_3420_);
lean_del_object(v___x_3406_);
lean_dec(v_a_3390_);
lean_dec(v_a_3383_);
v___x_3636_ = l_Lean_Meta_isMonad_x3f(v_fst_3403_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3729_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3729_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3729_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
if (lean_obj_tag(v_a_3637_) == 1)
{
lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_fst_3417_);
v___x_3643_ = v___x_3415_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_fst_3417_);
v___x_3643_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3645_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v_snd_3418_);
v___x_3645_ = v___x_3401_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_snd_3418_);
v___x_3645_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 1);
lean_ctor_set(v___x_3392_, 0, v_snd_3404_);
v___x_3647_ = v___x_3392_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_snd_3404_);
v___x_3647_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v_a_3673_; lean_object* v___x_3677_; 
v___x_3648_ = lean_box(0);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 1);
lean_ctor_set(v___x_3385_, 0, v_e_3354_);
v___x_3677_ = v___x_3385_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_e_3354_);
v___x_3677_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3676_;
}
v___jp_3649_:
{
if (v___y_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref(v___y_3650_);
lean_del_object(v___x_3639_);
v___x_3652_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3423_, v_a_3357_, v_a_3359_);
lean_dec(v_a_3423_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3652_, 0);
lean_dec(v_unused_3660_);
v___x_3654_ = v___x_3652_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_dec(v___x_3652_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3648_);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3648_);
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
v_a_3661_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3652_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3652_);
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
else
{
lean_object* v___x_3670_; 
lean_dec(v_a_3423_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 1);
lean_ctor_set(v___x_3639_, 0, v___y_3650_);
v___x_3670_ = v___x_3639_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___y_3650_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
v___jp_3672_:
{
uint8_t v___x_3674_; 
v___x_3674_ = l_Lean_Exception_isInterrupt(v_a_3673_);
if (v___x_3674_ == 0)
{
uint8_t v___x_3675_; 
lean_inc_ref(v_a_3673_);
v___x_3675_ = l_Lean_Exception_isRuntime(v_a_3673_);
v___y_3650_ = v_a_3673_;
v___y_3651_ = v___x_3675_;
goto v___jp_3649_;
}
else
{
v___y_3650_ = v_a_3673_;
v___y_3651_ = v___x_3674_;
goto v___jp_3649_;
}
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3678_ = lean_unsigned_to_nat(6u);
v___x_3679_ = lean_mk_empty_array_with_capacity(v___x_3678_);
v___x_3680_ = lean_array_push(v___x_3679_, v___x_3643_);
v___x_3681_ = lean_array_push(v___x_3680_, v___x_3645_);
v___x_3682_ = lean_array_push(v___x_3681_, v___x_3647_);
v___x_3683_ = lean_array_push(v___x_3682_, v___x_3648_);
v___x_3684_ = lean_array_push(v___x_3683_, v_a_3637_);
v___x_3685_ = lean_array_push(v___x_3684_, v___x_3677_);
v___x_3686_ = l_Lean_Meta_mkAppOptM(v___x_3641_, v___x_3685_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3705_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3705_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3705_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Meta_expandCoe(v_a_3687_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3703_; 
lean_del_object(v___x_3639_);
lean_dec(v_a_3423_);
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3703_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3703_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_fst_3696_; lean_object* v___x_3698_; 
v_fst_3696_ = lean_ctor_get(v_a_3692_, 0);
lean_inc(v_fst_3696_);
lean_dec(v_a_3692_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 1);
lean_ctor_set(v___x_3689_, 0, v_fst_3696_);
v___x_3698_ = v___x_3689_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_fst_3696_);
v___x_3698_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3700_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3698_);
v___x_3700_ = v___x_3694_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3704_; 
lean_del_object(v___x_3689_);
v_a_3704_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3704_);
lean_dec_ref(v___x_3691_);
v_a_3673_ = v_a_3704_;
goto v___jp_3672_;
}
}
}
else
{
lean_object* v_a_3706_; 
v_a_3706_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3686_);
v_a_3673_ = v_a_3706_;
goto v___jp_3672_;
}
}
}
}
}
}
else
{
lean_object* v___x_3711_; 
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3385_);
lean_dec_ref(v_e_3354_);
v___x_3711_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3423_, v_a_3357_, v_a_3359_);
lean_dec(v_a_3423_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3719_; 
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; 
v_unused_3720_ = lean_ctor_get(v___x_3711_, 0);
lean_dec(v_unused_3720_);
v___x_3713_ = v___x_3711_;
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v___x_3711_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3719_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = lean_box(0);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3715_);
v___x_3717_ = v___x_3713_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_a_3721_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3711_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3711_);
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
}
else
{
lean_dec(v_a_3423_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_dec(v_snd_3404_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_del_object(v___x_3385_);
lean_dec_ref(v_e_3354_);
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_a_3423_);
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3731_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3424_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3424_);
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
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3420_);
lean_dec(v_snd_3418_);
lean_dec(v_fst_3417_);
lean_del_object(v___x_3415_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3739_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3422_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3422_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
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
}
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_dec(v_a_3409_);
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3749_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3749_);
v___x_3751_ = v___x_3411_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
lean_dec(v_fst_3403_);
lean_del_object(v___x_3401_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3754_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3408_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3408_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec(v_a_3395_);
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v___x_3764_ = lean_box(0);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3764_);
v___x_3766_ = v___x_3397_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3392_);
lean_dec(v_a_3390_);
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3769_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3394_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3394_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_del_object(v___x_3385_);
lean_dec(v_a_3383_);
lean_dec_ref(v_e_3354_);
v_a_3778_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3387_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3387_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3787_, lean_object* v_expectedType_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3787_, v_expectedType_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3795_, lean_object* v_expectedType_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v___x_3802_; 
lean_inc_ref(v_expectedType_3796_);
lean_inc_ref(v_expr_3795_);
v___x_3802_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3795_, v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3882_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3882_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3882_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
if (lean_obj_tag(v_a_3803_) == 1)
{
lean_object* v_val_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_val_3807_ = lean_ctor_get(v_a_3803_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_a_3803_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3809_ = v_a_3803_;
v_isShared_3810_ = v_isSharedCheck_3819_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_val_3807_);
lean_dec(v_a_3803_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3819_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3811_ = lean_box(0);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_val_3807_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3814_);
v___x_3816_ = v___x_3805_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v___x_3820_; 
lean_del_object(v___x_3805_);
lean_dec(v_a_3803_);
lean_inc_ref(v_expectedType_3796_);
v___x_3820_ = l_Lean_Meta_whnfR(v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; uint8_t v___x_3822_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v___x_3820_);
v___x_3822_ = l_Lean_Expr_isForall(v_a_3821_);
lean_dec(v_a_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3795_, v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; 
lean_inc_ref(v_expr_3795_);
v___x_3824_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3795_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref(v___x_3824_);
if (lean_obj_tag(v_a_3825_) == 1)
{
lean_object* v_val_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3864_; 
v_val_3826_ = lean_ctor_get(v_a_3825_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_a_3825_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3828_ = v_a_3825_;
v_isShared_3829_ = v_isSharedCheck_3864_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_val_3826_);
lean_dec(v_a_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3864_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; 
lean_inc(v_a_3800_);
lean_inc_ref(v_a_3799_);
lean_inc(v_a_3798_);
lean_inc_ref(v_a_3797_);
lean_inc(v_val_3826_);
v___x_3830_ = lean_infer_type(v_val_3826_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
lean_inc_ref(v_expectedType_3796_);
v___x_3832_ = l_Lean_Meta_isExprDefEq(v_a_3831_, v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3847_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3847_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3847_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_unbox(v_a_3833_);
lean_dec(v_a_3833_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
lean_del_object(v___x_3835_);
lean_del_object(v___x_3828_);
lean_dec(v_val_3826_);
v___x_3838_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3795_, v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_val_3826_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3840_);
v___x_3842_ = v___x_3828_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3844_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3842_);
v___x_3844_ = v___x_3835_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_del_object(v___x_3828_);
lean_dec(v_val_3826_);
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_a_3848_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3832_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3832_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_del_object(v___x_3828_);
lean_dec(v_val_3826_);
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_a_3856_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3830_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3830_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
else
{
lean_object* v___x_3865_; 
lean_dec(v_a_3825_);
v___x_3865_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3795_, v_expectedType_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v___x_3865_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_a_3866_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3824_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3824_);
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
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_a_3874_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3820_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3820_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_expectedType_3796_);
lean_dec_ref(v_expr_3795_);
v_a_3883_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3802_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3802_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3891_, lean_object* v_expectedType_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3891_, v_expectedType_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3899_, lean_object* v_expectedType_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3899_, v_expectedType_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3931_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3931_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3931_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
switch(lean_obj_tag(v_a_3907_))
{
case 0:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_box(0);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3911_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
case 1:
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3926_; 
v_a_3915_ = lean_ctor_get(v_a_3907_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_a_3907_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3917_ = v_a_3907_;
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v_a_3907_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3926_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v_fst_3919_; lean_object* v___x_3921_; 
v_fst_3919_ = lean_ctor_get(v_a_3915_, 0);
lean_inc(v_fst_3919_);
lean_dec(v_a_3915_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v_fst_3919_);
v___x_3921_ = v___x_3917_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_fst_3919_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3921_);
v___x_3923_ = v___x_3909_;
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
}
}
default: 
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_box(2);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3927_);
v___x_3929_ = v___x_3909_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
v_a_3932_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3906_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3906_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3940_, lean_object* v_expectedType_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_coerce_x3f(v_expr_3940_, v_expectedType_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
return v_res_3947_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_coeDeclAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_coeDeclAttr);
lean_dec_ref(res);
res = l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
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
