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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_options_179_; uint8_t v_hasTrace_180_; 
v_options_179_ = lean_ctor_get(v___y_177_, 2);
v_hasTrace_180_ = lean_ctor_get_uint8(v_options_179_, sizeof(void*)*1);
if (v_hasTrace_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_cls_175_);
v___x_181_ = lean_box(v_hasTrace_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___y_176_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
else
{
lean_object* v_inheritedTraceOptions_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_inheritedTraceOptions_184_ = lean_ctor_get(v___y_177_, 13);
v___x_185_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_186_ = l_Lean_Name_append(v___x_185_, v_cls_175_);
v___x_187_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_184_, v_options_179_, v___x_186_);
lean_dec(v___x_186_);
v___x_188_ = lean_box(v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___y_176_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(v_cls_191_, v___y_192_, v___y_193_);
lean_dec_ref(v___y_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_keys_196_, lean_object* v_i_197_, lean_object* v_k_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_keys_196_);
v___x_200_ = lean_nat_dec_lt(v_i_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v_i_197_);
return v___x_200_;
}
else
{
lean_object* v_k_x27_201_; uint8_t v___x_202_; 
v_k_x27_201_ = lean_array_fget_borrowed(v_keys_196_, v_i_197_);
v___x_202_ = l_Lean_instBEqExtraModUse_beq(v_k_198_, v_k_x27_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_i_197_, v___x_203_);
lean_dec(v_i_197_);
v_i_197_ = v___x_204_;
goto _start;
}
else
{
lean_dec(v_i_197_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_keys_206_, lean_object* v_i_207_, lean_object* v_k_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_206_, v_i_207_, v_k_208_);
lean_dec_ref(v_k_208_);
lean_dec_ref(v_keys_206_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; 
v___x_211_ = ((size_t)5ULL);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_shift_left(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; 
v___x_214_ = ((size_t)1ULL);
v___x_215_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_216_ = lean_usize_sub(v___x_215_, v___x_214_);
return v___x_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_217_, size_t v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v_es_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v_j_225_; lean_object* v___x_226_; 
v_es_220_ = lean_ctor_get(v_x_217_, 0);
lean_inc_ref(v_es_220_);
lean_dec_ref(v_x_217_);
v___x_221_ = lean_box(2);
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_224_ = lean_usize_land(v_x_218_, v___x_223_);
v_j_225_ = lean_usize_to_nat(v___x_224_);
v___x_226_ = lean_array_get(v___x_221_, v_es_220_, v_j_225_);
lean_dec(v_j_225_);
lean_dec_ref(v_es_220_);
switch(lean_obj_tag(v___x_226_))
{
case 0:
{
lean_object* v_key_227_; uint8_t v___x_228_; 
v_key_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_key_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = l_Lean_instBEqExtraModUse_beq(v_x_219_, v_key_227_);
lean_dec(v_key_227_);
return v___x_228_;
}
case 1:
{
lean_object* v_node_229_; size_t v___x_230_; 
v_node_229_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_node_229_);
lean_dec_ref(v___x_226_);
v___x_230_ = lean_usize_shift_right(v_x_218_, v___x_222_);
v_x_217_ = v_node_229_;
v_x_218_ = v___x_230_;
goto _start;
}
default: 
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
}
else
{
lean_object* v_ks_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_ks_233_ = lean_ctor_get(v_x_217_, 0);
lean_inc_ref(v_ks_233_);
lean_dec_ref(v_x_217_);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ks_233_, v___x_234_, v_x_219_);
lean_dec_ref(v_ks_233_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
size_t v_x_35972__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_x_35972__boxed_239_ = lean_unbox_usize(v_x_237_);
lean_dec(v_x_237_);
v_res_240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_236_, v_x_35972__boxed_239_, v_x_238_);
lean_dec_ref(v_x_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint64_t v___x_244_; size_t v___x_245_; uint8_t v___x_246_; 
v___x_244_ = l_Lean_instHashableExtraModUse_hash(v_x_243_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_242_, v___x_245_, v_x_243_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_247_, v_x_248_);
lean_dec_ref(v_x_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(lean_object* v_msgData_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_env_258_; lean_object* v___x_259_; lean_object* v_mctx_260_; lean_object* v_lctx_261_; lean_object* v_options_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_257_ = lean_st_ref_get(v___y_255_);
v_env_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_env_258_);
lean_dec(v___x_257_);
v___x_259_ = lean_st_ref_get(v___y_253_);
v_mctx_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_mctx_260_);
lean_dec(v___x_259_);
v_lctx_261_ = lean_ctor_get(v___y_252_, 2);
v_options_262_ = lean_ctor_get(v___y_254_, 2);
lean_inc_ref(v_options_262_);
lean_inc_ref(v_lctx_261_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_258_);
lean_ctor_set(v___x_263_, 1, v_mctx_260_);
lean_ctor_set(v___x_263_, 2, v_lctx_261_);
lean_ctor_set(v___x_263_, 3, v_options_262_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_251_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(v_msgData_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_273_; double v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_float_of_nat(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(lean_object* v_cls_278_, lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_ref_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_333_; 
v_ref_286_ = lean_ctor_get(v___y_283_, 5);
v___x_287_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(v_msg_279_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_333_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_333_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_333_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v_traceState_293_; lean_object* v_env_294_; lean_object* v_nextMacroScope_295_; lean_object* v_ngen_296_; lean_object* v_auxDeclNGen_297_; lean_object* v_cache_298_; lean_object* v_messages_299_; lean_object* v_infoState_300_; lean_object* v_snapshotTasks_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_332_; 
v___x_292_ = lean_st_ref_take(v___y_284_);
v_traceState_293_ = lean_ctor_get(v___x_292_, 4);
v_env_294_ = lean_ctor_get(v___x_292_, 0);
v_nextMacroScope_295_ = lean_ctor_get(v___x_292_, 1);
v_ngen_296_ = lean_ctor_get(v___x_292_, 2);
v_auxDeclNGen_297_ = lean_ctor_get(v___x_292_, 3);
v_cache_298_ = lean_ctor_get(v___x_292_, 5);
v_messages_299_ = lean_ctor_get(v___x_292_, 6);
v_infoState_300_ = lean_ctor_get(v___x_292_, 7);
v_snapshotTasks_301_ = lean_ctor_get(v___x_292_, 8);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_332_ == 0)
{
v___x_303_ = v___x_292_;
v_isShared_304_ = v_isSharedCheck_332_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snapshotTasks_301_);
lean_inc(v_infoState_300_);
lean_inc(v_messages_299_);
lean_inc(v_cache_298_);
lean_inc(v_traceState_293_);
lean_inc(v_auxDeclNGen_297_);
lean_inc(v_ngen_296_);
lean_inc(v_nextMacroScope_295_);
lean_inc(v_env_294_);
lean_dec(v___x_292_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_332_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint64_t v_tid_305_; lean_object* v_traces_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_331_; 
v_tid_305_ = lean_ctor_get_uint64(v_traceState_293_, sizeof(void*)*1);
v_traces_306_ = lean_ctor_get(v_traceState_293_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_traceState_293_);
if (v_isSharedCheck_331_ == 0)
{
v___x_308_ = v_traceState_293_;
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_traces_306_);
lean_dec(v_traceState_293_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; double v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__0);
v___x_312_ = 0;
v___x_313_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1));
v___x_314_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_314_, 0, v_cls_278_);
lean_ctor_set(v___x_314_, 1, v___x_310_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_ctor_set_float(v___x_314_, sizeof(void*)*3, v___x_311_);
lean_ctor_set_float(v___x_314_, sizeof(void*)*3 + 8, v___x_311_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*3 + 16, v___x_312_);
v___x_315_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__2));
v___x_316_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v_a_288_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_inc(v_ref_286_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_ref_286_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_PersistentArray_push___redArg(v_traces_306_, v___x_317_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_318_);
v___x_320_ = v___x_308_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_318_);
lean_ctor_set_uint64(v_reuseFailAlloc_330_, sizeof(void*)*1, v_tid_305_);
v___x_320_ = v_reuseFailAlloc_330_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v___x_320_);
v___x_322_ = v___x_303_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_env_294_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_nextMacroScope_295_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_ngen_296_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_auxDeclNGen_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v_cache_298_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_messages_299_);
lean_ctor_set(v_reuseFailAlloc_329_, 7, v_infoState_300_);
lean_ctor_set(v_reuseFailAlloc_329_, 8, v_snapshotTasks_301_);
v___x_322_ = v_reuseFailAlloc_329_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_323_ = lean_st_ref_set(v___y_284_, v___x_322_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___y_280_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_325_);
v___x_327_ = v___x_290_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(v_cls_334_, v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1));
v___x_346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0));
v___x_347_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
v___x_354_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
lean_ctor_set(v___x_354_, 4, v___x_353_);
lean_ctor_set(v___x_354_, 5, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3___closed__1));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(lean_object* v_mod_376_, uint8_t v_isMeta_377_, lean_object* v_hint_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_env_386_; uint8_t v_isExporting_387_; lean_object* v___x_388_; lean_object* v_env_389_; lean_object* v___x_390_; lean_object* v_entry_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_env_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_385_);
v_isExporting_387_ = lean_ctor_get_uint8(v_env_386_, sizeof(void*)*8);
lean_dec_ref(v_env_386_);
v___x_388_ = lean_st_ref_get(v___y_383_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
v___x_390_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
lean_inc(v_mod_376_);
v_entry_391_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_391_, 0, v_mod_376_);
lean_ctor_set_uint8(v_entry_391_, sizeof(void*)*1, v_isExporting_387_);
lean_ctor_set_uint8(v_entry_391_, sizeof(void*)*1 + 1, v_isMeta_377_);
v___x_392_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_393_ = lean_box(1);
v___x_394_ = lean_box(0);
v___x_439_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_390_, v___x_392_, v_env_389_, v___x_393_, v___x_394_);
v___x_440_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_439_, v_entry_391_);
if (v___x_440_ == 0)
{
lean_object* v_cls_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_484_; 
v_cls_441_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8));
v___x_442_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(v_cls_441_, v___y_379_, v___y_382_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v_fst_444_ = lean_ctor_get(v_a_443_, 0);
v_snd_445_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_484_ == 0)
{
v___x_447_ = v_a_443_;
v_isShared_448_ = v_isSharedCheck_484_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v_a_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_484_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___x_472_; 
v___x_472_ = lean_unbox(v_fst_444_);
lean_dec(v_fst_444_);
if (v___x_472_ == 0)
{
lean_del_object(v___x_447_);
lean_dec(v_hint_378_);
lean_dec(v_mod_376_);
v___y_396_ = v_snd_445_;
v___y_397_ = v___y_381_;
v___y_398_ = v___y_383_;
goto v___jp_395_;
}
else
{
lean_object* v___x_473_; lean_object* v___y_475_; 
v___x_473_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15);
if (v_isExporting_387_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20));
v___y_475_ = v___x_482_;
goto v___jp_474_;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21));
v___y_475_ = v___x_483_;
goto v___jp_474_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = l_Lean_stringToMessageData(v___y_475_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_473_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
if (v_isMeta_377_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18));
v___y_459_ = v___x_479_;
v___y_460_ = v___x_480_;
goto v___jp_458_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19));
v___y_459_ = v___x_479_;
v___y_460_ = v___x_481_;
goto v___jp_458_;
}
}
}
v___jp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 7);
lean_ctor_set(v___x_447_, 1, v___y_451_);
lean_ctor_set(v___x_447_, 0, v___y_450_);
v___x_453_ = v___x_447_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___y_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___y_451_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3(v_cls_441_, v___x_453_, v_snd_445_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_snd_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref(v___x_454_);
v_snd_456_ = lean_ctor_get(v_a_455_, 1);
lean_inc(v_snd_456_);
lean_dec(v_a_455_);
v___y_396_ = v_snd_456_;
v___y_397_ = v___y_381_;
v___y_398_ = v___y_383_;
goto v___jp_395_;
}
else
{
lean_dec_ref(v_entry_391_);
return v___x_454_;
}
}
}
v___jp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_461_ = l_Lean_stringToMessageData(v___y_460_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___y_459_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_MessageData_ofName(v_mod_376_);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_Name_isAnonymous(v_hint_378_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
v___x_469_ = l_Lean_MessageData_ofName(v_hint_378_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___y_450_ = v___x_466_;
v___y_451_ = v___x_470_;
goto v___jp_449_;
}
else
{
lean_object* v___x_471_; 
lean_dec(v_hint_378_);
v___x_471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
v___y_450_ = v___x_466_;
v___y_451_ = v___x_471_;
goto v___jp_449_;
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v_entry_391_);
lean_dec(v_hint_378_);
lean_dec(v_mod_376_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___y_379_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
v___jp_395_:
{
lean_object* v___x_399_; lean_object* v_toEnvExtension_400_; lean_object* v_env_401_; lean_object* v_nextMacroScope_402_; lean_object* v_ngen_403_; lean_object* v_auxDeclNGen_404_; lean_object* v_traceState_405_; lean_object* v_messages_406_; lean_object* v_infoState_407_; lean_object* v_snapshotTasks_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_437_; 
v___x_399_ = lean_st_ref_take(v___y_398_);
v_toEnvExtension_400_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_toEnvExtension_400_);
v_env_401_ = lean_ctor_get(v___x_399_, 0);
v_nextMacroScope_402_ = lean_ctor_get(v___x_399_, 1);
v_ngen_403_ = lean_ctor_get(v___x_399_, 2);
v_auxDeclNGen_404_ = lean_ctor_get(v___x_399_, 3);
v_traceState_405_ = lean_ctor_get(v___x_399_, 4);
v_messages_406_ = lean_ctor_get(v___x_399_, 6);
v_infoState_407_ = lean_ctor_get(v___x_399_, 7);
v_snapshotTasks_408_ = lean_ctor_get(v___x_399_, 8);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_399_, 5);
lean_dec(v_unused_438_);
v___x_410_ = v___x_399_;
v_isShared_411_ = v_isSharedCheck_437_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snapshotTasks_408_);
lean_inc(v_infoState_407_);
lean_inc(v_messages_406_);
lean_inc(v_traceState_405_);
lean_inc(v_auxDeclNGen_404_);
lean_inc(v_ngen_403_);
lean_inc(v_nextMacroScope_402_);
lean_inc(v_env_401_);
lean_dec(v___x_399_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_437_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_asyncMode_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_asyncMode_412_ = lean_ctor_get(v_toEnvExtension_400_, 2);
lean_inc(v_asyncMode_412_);
lean_dec_ref(v_toEnvExtension_400_);
v___x_413_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_392_, v_env_401_, v_entry_391_, v_asyncMode_412_, v___x_394_);
lean_dec(v_asyncMode_412_);
v___x_414_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 5, v___x_414_);
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_nextMacroScope_402_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_ngen_403_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_auxDeclNGen_404_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_traceState_405_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v_messages_406_);
lean_ctor_set(v_reuseFailAlloc_436_, 7, v_infoState_407_);
lean_ctor_set(v_reuseFailAlloc_436_, 8, v_snapshotTasks_408_);
v___x_416_ = v_reuseFailAlloc_436_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_mctx_419_; lean_object* v_zetaDeltaFVarIds_420_; lean_object* v_postponed_421_; lean_object* v_diag_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_434_; 
v___x_417_ = lean_st_ref_set(v___y_398_, v___x_416_);
v___x_418_ = lean_st_ref_take(v___y_397_);
v_mctx_419_ = lean_ctor_get(v___x_418_, 0);
v_zetaDeltaFVarIds_420_ = lean_ctor_get(v___x_418_, 2);
v_postponed_421_ = lean_ctor_get(v___x_418_, 3);
v_diag_422_ = lean_ctor_get(v___x_418_, 4);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_418_, 1);
lean_dec(v_unused_435_);
v___x_424_ = v___x_418_;
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_diag_422_);
lean_inc(v_postponed_421_);
lean_inc(v_zetaDeltaFVarIds_420_);
lean_inc(v_mctx_419_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_mctx_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_zetaDeltaFVarIds_420_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_postponed_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_diag_422_);
v___x_428_ = v_reuseFailAlloc_433_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_st_ref_set(v___y_397_, v___x_428_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___y_396_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(lean_object* v_mod_488_, lean_object* v_isMeta_489_, lean_object* v_hint_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v_isMeta_boxed_497_; lean_object* v_res_498_; 
v_isMeta_boxed_497_ = lean_unbox(v_isMeta_489_);
v_res_498_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_488_, v_isMeta_boxed_497_, v_hint_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(lean_object* v_a_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v_key_502_; lean_object* v_value_503_; lean_object* v_tail_504_; uint8_t v___x_505_; 
v_key_502_ = lean_ctor_get(v_x_500_, 0);
v_value_503_ = lean_ctor_get(v_x_500_, 1);
v_tail_504_ = lean_ctor_get(v_x_500_, 2);
v___x_505_ = lean_name_eq(v_key_502_, v_a_499_);
if (v___x_505_ == 0)
{
v_x_500_ = v_tail_504_;
goto _start;
}
else
{
lean_object* v___x_507_; 
lean_inc(v_value_503_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v_value_503_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_a_508_);
return v_res_510_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_511_; uint64_t v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(1723u);
v___x_512_ = lean_uint64_of_nat(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_buckets_515_; lean_object* v___x_516_; uint64_t v___y_518_; 
v_buckets_515_ = lean_ctor_get(v_m_513_, 1);
v___x_516_ = lean_array_get_size(v_buckets_515_);
if (lean_obj_tag(v_a_514_) == 0)
{
uint64_t v___x_532_; 
v___x_532_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
v___y_518_ = v___x_532_;
goto v___jp_517_;
}
else
{
uint64_t v_hash_533_; 
v_hash_533_ = lean_ctor_get_uint64(v_a_514_, sizeof(void*)*2);
v___y_518_ = v_hash_533_;
goto v___jp_517_;
}
v___jp_517_:
{
uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v_fold_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_519_ = 32ULL;
v___x_520_ = lean_uint64_shift_right(v___y_518_, v___x_519_);
v_fold_521_ = lean_uint64_xor(v___y_518_, v___x_520_);
v___x_522_ = 16ULL;
v___x_523_ = lean_uint64_shift_right(v_fold_521_, v___x_522_);
v___x_524_ = lean_uint64_xor(v_fold_521_, v___x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = lean_usize_of_nat(v___x_516_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_usize_land(v___x_525_, v___x_528_);
v___x_530_ = lean_array_uget_borrowed(v_buckets_515_, v___x_529_);
v___x_531_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_514_, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_m_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(lean_object* v___x_537_, lean_object* v_declName_538_, lean_object* v_as_539_, size_t v_sz_540_, size_t v_i_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_lt(v_i_541_, v_sz_540_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_declName_538_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_b_542_);
lean_ctor_set(v___x_550_, 1, v___y_543_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v_modules_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v_toImport_557_; lean_object* v_module_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v___x_552_ = l_Lean_Environment_header(v___x_537_);
v_modules_553_ = lean_ctor_get(v___x_552_, 3);
lean_inc_ref(v_modules_553_);
lean_dec_ref(v___x_552_);
v___x_554_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_555_ = lean_array_uget_borrowed(v_as_539_, v_i_541_);
v___x_556_ = lean_array_get(v___x_554_, v_modules_553_, v_a_555_);
lean_dec_ref(v_modules_553_);
v_toImport_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc_ref(v_toImport_557_);
lean_dec(v___x_556_);
v_module_558_ = lean_ctor_get(v_toImport_557_, 0);
lean_inc(v_module_558_);
lean_dec_ref(v_toImport_557_);
v___x_559_ = 0;
lean_inc(v_declName_538_);
v___x_560_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_558_, v___x_559_, v_declName_538_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_snd_562_; lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___x_560_);
v_snd_562_ = lean_ctor_get(v_a_561_, 1);
lean_inc(v_snd_562_);
lean_dec(v_a_561_);
v___x_563_ = lean_box(0);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_541_, v___x_564_);
v_i_541_ = v___x_565_;
v_b_542_ = v___x_563_;
v___y_543_ = v_snd_562_;
goto _start;
}
else
{
lean_dec(v_declName_538_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(lean_object* v___x_567_, lean_object* v_declName_568_, lean_object* v_as_569_, lean_object* v_sz_570_, lean_object* v_i_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_570_);
lean_dec(v_sz_570_);
v_i_boxed_580_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_567_, v_declName_568_, v_as_569_, v_sz_boxed_579_, v_i_boxed_580_, v_b_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_569_);
lean_dec_ref(v___x_567_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1));
v___x_585_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0));
v___x_586_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_585_, v___x_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(lean_object* v_declName_589_, uint8_t v_isMeta_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v_env_602_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___x_627_; 
v___x_597_ = lean_st_ref_get(v___y_595_);
v_env_602_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_602_);
lean_dec(v___x_597_);
v___x_627_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_602_, v_declName_589_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref(v_env_602_);
lean_dec(v_declName_589_);
goto v___jp_598_;
}
else
{
lean_object* v_val_628_; lean_object* v___x_629_; lean_object* v_modules_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_val_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = l_Lean_Environment_header(v_env_602_);
v_modules_630_ = lean_ctor_get(v___x_629_, 3);
lean_inc_ref(v_modules_630_);
lean_dec_ref(v___x_629_);
v___x_631_ = lean_array_get_size(v_modules_630_);
v___x_632_ = lean_nat_dec_lt(v_val_628_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec_ref(v_modules_630_);
lean_dec(v_val_628_);
lean_dec_ref(v_env_602_);
lean_dec(v_declName_589_);
goto v___jp_598_;
}
else
{
lean_object* v___x_633_; lean_object* v_env_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___y_638_; 
v___x_633_ = lean_st_ref_get(v___y_595_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
v___x_635_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
v___x_636_ = lean_array_fget(v_modules_630_, v_val_628_);
lean_dec(v_val_628_);
lean_dec_ref(v_modules_630_);
if (v_isMeta_590_ == 0)
{
lean_dec_ref(v_env_634_);
v___y_638_ = v_isMeta_590_;
goto v___jp_637_;
}
else
{
uint8_t v___x_651_; 
lean_inc(v_declName_589_);
v___x_651_ = l_Lean_isMarkedMeta(v_env_634_, v_declName_589_);
if (v___x_651_ == 0)
{
v___y_638_ = v_isMeta_590_;
goto v___jp_637_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
v___y_638_ = v___x_652_;
goto v___jp_637_;
}
}
v___jp_637_:
{
lean_object* v_toImport_639_; lean_object* v_module_640_; lean_object* v___x_641_; 
v_toImport_639_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_toImport_639_);
lean_dec(v___x_636_);
v_module_640_ = lean_ctor_get(v_toImport_639_, 0);
lean_inc(v_module_640_);
lean_dec_ref(v_toImport_639_);
lean_inc(v_declName_589_);
v___x_641_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_640_, v___y_638_, v_declName_589_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_snd_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref(v___x_641_);
v_snd_643_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_643_);
lean_dec(v_a_642_);
v___x_644_ = l_Lean_indirectModUseExt;
v___x_645_ = lean_box(1);
v___x_646_ = lean_box(0);
lean_inc_ref(v_env_602_);
v___x_647_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_635_, v___x_644_, v_env_602_, v___x_645_, v___x_646_);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_647_, v_declName_589_);
lean_dec(v___x_647_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3));
v___y_604_ = v_snd_643_;
v___y_605_ = v___x_649_;
goto v___jp_603_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v___x_648_);
v___y_604_ = v_snd_643_;
v___y_605_ = v_val_650_;
goto v___jp_603_;
}
}
else
{
lean_dec_ref(v_env_602_);
lean_dec(v_declName_589_);
return v___x_641_;
}
}
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___y_591_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
v___jp_603_:
{
lean_object* v___x_606_; size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_box(0);
v_sz_607_ = lean_array_size(v___y_605_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_602_, v_declName_589_, v___y_605_, v_sz_607_, v___x_608_, v___x_606_, v___y_604_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec_ref(v___y_605_);
lean_dec_ref(v_env_602_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_626_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_626_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_snd_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_624_; 
v_snd_614_ = lean_ctor_get(v_a_610_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v_a_610_, 0);
lean_dec(v_unused_625_);
v___x_616_ = v_a_610_;
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_614_);
lean_dec(v_a_610_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_606_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_snd_614_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_619_);
v___x_621_ = v___x_612_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
else
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(lean_object* v_declName_653_, lean_object* v_isMeta_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v_isMeta_boxed_661_; lean_object* v_res_662_; 
v_isMeta_boxed_661_ = lean_unbox(v_isMeta_654_);
v_res_662_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_declName_653_, v_isMeta_boxed_661_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1(lean_object* v_e_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___y_678_; lean_object* v_f_682_; uint8_t v___x_683_; 
v_f_682_ = l_Lean_Expr_getAppFn(v_e_670_);
v___x_683_ = l_Lean_Expr_isConst(v_f_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_f_682_);
lean_dec_ref(v_e_670_);
v___y_678_ = v___y_671_;
goto v___jp_677_;
}
else
{
lean_object* v___x_684_; lean_object* v_env_685_; lean_object* v_declName_686_; uint8_t v___x_687_; 
v___x_684_ = lean_st_ref_get(v___y_675_);
v_env_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_env_685_);
lean_dec(v___x_684_);
v_declName_686_ = l_Lean_Expr_constName_x21(v_f_682_);
lean_dec_ref(v_f_682_);
lean_inc(v_declName_686_);
v___x_687_ = l_Lean_Meta_isCoeDecl(v_env_685_, v_declName_686_);
if (v___x_687_ == 0)
{
lean_dec(v_declName_686_);
lean_dec_ref(v_e_670_);
v___y_678_ = v___y_671_;
goto v___jp_677_;
}
else
{
lean_object* v___x_688_; 
lean_inc(v_declName_686_);
lean_inc_ref(v_e_670_);
v___x_688_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(v_e_670_, v_declName_686_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; uint8_t v___x_690_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = 0;
v___x_691_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_689_, v___x_690_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_744_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v_snd_693_ = lean_ctor_get(v_a_692_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_a_692_, 0);
lean_dec(v_unused_745_);
v___x_695_ = v_a_692_;
v_isShared_696_ = v_isSharedCheck_744_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_dec(v_a_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_744_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; 
lean_inc_ref(v_e_670_);
v___x_697_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_670_, v___x_690_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_735_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_735_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_735_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_735_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
if (lean_obj_tag(v_a_698_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_734_; 
v_val_702_ = lean_ctor_get(v_a_698_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_698_);
if (v_isSharedCheck_734_ == 0)
{
v___x_704_ = v_a_698_;
v_isShared_705_ = v_isSharedCheck_734_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_val_702_);
lean_dec(v_a_698_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_734_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___y_707_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__3));
v___x_719_ = lean_name_eq(v_declName_686_, v___x_718_);
lean_dec(v_declName_686_);
if (v___x_719_ == 0)
{
lean_dec_ref(v_e_670_);
v___y_707_ = v_snd_693_;
goto v___jp_706_;
}
else
{
lean_object* v_dummy_720_; lean_object* v_nargs_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_dummy_720_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_721_ = l_Lean_Expr_getAppNumArgs(v_e_670_);
lean_inc(v_nargs_721_);
v___x_722_ = lean_mk_array(v_nargs_721_, v_dummy_720_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_sub(v_nargs_721_, v___x_723_);
lean_dec(v_nargs_721_);
v___x_725_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_670_, v___x_722_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_array_get_size(v___x_725_);
v___x_728_ = lean_nat_dec_lt(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec_ref(v___x_725_);
v___y_707_ = v_snd_693_;
goto v___jp_706_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_array_fget(v___x_725_, v___x_726_);
lean_dec_ref(v___x_725_);
v___x_730_ = l_Lean_Expr_getAppFn(v___x_729_);
lean_dec(v___x_729_);
v___x_731_ = l_Lean_Expr_isConst(v___x_730_);
if (v___x_731_ == 0)
{
lean_dec_ref(v___x_730_);
v___y_707_ = v_snd_693_;
goto v___jp_706_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_Expr_constName_x21(v___x_730_);
lean_dec_ref(v___x_730_);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_snd_693_);
v___y_707_ = v___x_733_;
goto v___jp_706_;
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l_Lean_Expr_headBeta(v_val_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_717_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___y_707_);
lean_ctor_set(v___x_695_, 0, v___x_710_);
v___x_712_ = v___x_695_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___y_707_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_712_);
v___x_714_ = v___x_700_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_700_);
lean_dec(v_a_698_);
lean_del_object(v___x_695_);
lean_dec(v_declName_686_);
lean_dec_ref(v_e_670_);
v___y_678_ = v_snd_693_;
goto v___jp_677_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_del_object(v___x_695_);
lean_dec(v_snd_693_);
lean_dec(v_declName_686_);
lean_dec_ref(v_e_670_);
v_a_736_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_697_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_697_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_declName_686_);
lean_dec_ref(v_e_670_);
v_a_746_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_691_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_691_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_declName_686_);
lean_dec(v___y_671_);
lean_dec_ref(v_e_670_);
v_a_754_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_688_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_688_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((lean_object*)(l_Lean_Meta_expandCoe___lam__1___closed__0));
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___y_678_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___lam__1___boxed(lean_object* v_e_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_expandCoe___lam__1(v_e_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0(lean_object* v_k_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_771_);
v___x_779_ = lean_apply_8(v_k_770_, v_b_773_, v___y_771_, v___y_772_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0___boxed(lean_object* v_k_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0(v_k_780_, v___y_781_, v___y_782_, v_b_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_781_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(lean_object* v_name_790_, lean_object* v_type_791_, lean_object* v_val_792_, lean_object* v_k_793_, uint8_t v_nondep_794_, uint8_t v_kind_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___f_803_; lean_object* v___x_804_; 
lean_inc(v___y_796_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_803_, 0, v_k_793_);
lean_closure_set(v___f_803_, 1, v___y_796_);
lean_closure_set(v___f_803_, 2, v___y_797_);
v___x_804_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_790_, v_type_791_, v_val_792_, v___f_803_, v_nondep_794_, v_kind_795_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_804_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_804_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_name_821_, lean_object* v_type_822_, lean_object* v_val_823_, lean_object* v_k_824_, lean_object* v_nondep_825_, lean_object* v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
uint8_t v_nondep_boxed_834_; uint8_t v_kind_boxed_835_; lean_object* v_res_836_; 
v_nondep_boxed_834_ = lean_unbox(v_nondep_825_);
v_kind_boxed_835_ = lean_unbox(v_kind_826_);
v_res_836_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(v_name_821_, v_type_822_, v_val_823_, v_k_824_, v_nondep_boxed_834_, v_kind_boxed_835_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_827_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(lean_object* v_name_837_, uint8_t v_bi_838_, lean_object* v_type_839_, lean_object* v_k_840_, uint8_t v_kind_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___x_850_; 
lean_inc(v___y_842_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_849_, 0, v_k_840_);
lean_closure_set(v___f_849_, 1, v___y_842_);
lean_closure_set(v___f_849_, 2, v___y_843_);
v___x_850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_837_, v_bi_838_, v_type_839_, v___f_849_, v_kind_841_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
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
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_850_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_850_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg___boxed(lean_object* v_name_867_, lean_object* v_bi_868_, lean_object* v_type_869_, lean_object* v_k_870_, lean_object* v_kind_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_bi_boxed_879_; uint8_t v_kind_boxed_880_; lean_object* v_res_881_; 
v_bi_boxed_879_ = lean_unbox(v_bi_868_);
v_kind_boxed_880_ = lean_unbox(v_kind_871_);
v_res_881_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_name_867_, v_bi_boxed_879_, v_type_869_, v_k_870_, v_kind_boxed_880_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_872_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(lean_object* v___x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_882_);
lean_ctor_set(v___x_889_, 1, v___y_883_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed(lean_object* v___x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2(v___x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29___redArg(lean_object* v_x_899_, lean_object* v_x_900_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28___redArg(lean_object* v_i_927_, lean_object* v_source_928_, lean_object* v_target_929_){
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
v_target_935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29___redArg(v_target_929_, v_es_932_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(lean_object* v_data_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_nbuckets_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_940_ = lean_array_get_size(v_data_939_);
v___x_941_ = lean_unsigned_to_nat(2u);
v_nbuckets_942_ = lean_nat_mul(v___x_940_, v___x_941_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_box(0);
v___x_945_ = lean_mk_array(v_nbuckets_942_, v___x_944_);
v___x_946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28___redArg(v___x_943_, v_data_939_, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(lean_object* v_a_947_, lean_object* v_b_948_, lean_object* v_x_949_){
_start:
{
if (lean_obj_tag(v_x_949_) == 0)
{
lean_dec(v_b_948_);
lean_dec_ref(v_a_947_);
return v_x_949_;
}
else
{
lean_object* v_key_950_; lean_object* v_value_951_; lean_object* v_tail_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_964_; 
v_key_950_ = lean_ctor_get(v_x_949_, 0);
v_value_951_ = lean_ctor_get(v_x_949_, 1);
v_tail_952_ = lean_ctor_get(v_x_949_, 2);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_949_);
if (v_isSharedCheck_964_ == 0)
{
v___x_954_ = v_x_949_;
v_isShared_955_ = v_isSharedCheck_964_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_tail_952_);
lean_inc(v_value_951_);
lean_inc(v_key_950_);
lean_dec(v_x_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_964_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_ExprStructEq_beq(v_key_950_, v_a_947_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_a_947_, v_b_948_, v_tail_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 2, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_key_950_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_value_951_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v_value_951_);
lean_dec(v_key_950_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_b_948_);
lean_ctor_set(v___x_954_, 0, v_a_947_);
v___x_962_ = v___x_954_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_947_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_b_948_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_tail_952_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(lean_object* v_a_965_, lean_object* v_x_966_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
uint8_t v___x_967_; 
v___x_967_ = 0;
return v___x_967_;
}
else
{
lean_object* v_key_968_; lean_object* v_tail_969_; uint8_t v___x_970_; 
v_key_968_ = lean_ctor_get(v_x_966_, 0);
v_tail_969_ = lean_ctor_get(v_x_966_, 2);
v___x_970_ = l_Lean_ExprStructEq_beq(v_key_968_, v_a_965_);
if (v___x_970_ == 0)
{
v_x_966_ = v_tail_969_;
goto _start;
}
else
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg___boxed(lean_object* v_a_972_, lean_object* v_x_973_){
_start:
{
uint8_t v_res_974_; lean_object* v_r_975_; 
v_res_974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(v_a_972_, v_x_973_);
lean_dec(v_x_973_);
lean_dec_ref(v_a_972_);
v_r_975_ = lean_box(v_res_974_);
return v_r_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(lean_object* v_m_976_, lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
lean_object* v_size_979_; lean_object* v_buckets_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1023_; 
v_size_979_ = lean_ctor_get(v_m_976_, 0);
v_buckets_980_ = lean_ctor_get(v_m_976_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_m_976_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_982_ = v_m_976_;
v_isShared_983_ = v_isSharedCheck_1023_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_buckets_980_);
lean_inc(v_size_979_);
lean_dec(v_m_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1023_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; uint64_t v___x_985_; uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v_fold_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v_bkt_997_; uint8_t v___x_998_; 
v___x_984_ = lean_array_get_size(v_buckets_980_);
v___x_985_ = l_Lean_ExprStructEq_hash(v_a_977_);
v___x_986_ = 32ULL;
v___x_987_ = lean_uint64_shift_right(v___x_985_, v___x_986_);
v_fold_988_ = lean_uint64_xor(v___x_985_, v___x_987_);
v___x_989_ = 16ULL;
v___x_990_ = lean_uint64_shift_right(v_fold_988_, v___x_989_);
v___x_991_ = lean_uint64_xor(v_fold_988_, v___x_990_);
v___x_992_ = lean_uint64_to_usize(v___x_991_);
v___x_993_ = lean_usize_of_nat(v___x_984_);
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_sub(v___x_993_, v___x_994_);
v___x_996_ = lean_usize_land(v___x_992_, v___x_995_);
v_bkt_997_ = lean_array_uget_borrowed(v_buckets_980_, v___x_996_);
v___x_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(v_a_977_, v_bkt_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v_size_x27_1000_; lean_object* v___x_1001_; lean_object* v_buckets_x27_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v_size_x27_1000_ = lean_nat_add(v_size_979_, v___x_999_);
lean_dec(v_size_979_);
lean_inc(v_bkt_997_);
v___x_1001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1001_, 0, v_a_977_);
lean_ctor_set(v___x_1001_, 1, v_b_978_);
lean_ctor_set(v___x_1001_, 2, v_bkt_997_);
v_buckets_x27_1002_ = lean_array_uset(v_buckets_980_, v___x_996_, v___x_1001_);
v___x_1003_ = lean_unsigned_to_nat(4u);
v___x_1004_ = lean_nat_mul(v_size_x27_1000_, v___x_1003_);
v___x_1005_ = lean_unsigned_to_nat(3u);
v___x_1006_ = lean_nat_div(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_array_get_size(v_buckets_x27_1002_);
v___x_1008_ = lean_nat_dec_le(v___x_1006_, v___x_1007_);
lean_dec(v___x_1006_);
if (v___x_1008_ == 0)
{
lean_object* v_val_1009_; lean_object* v___x_1011_; 
v_val_1009_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_buckets_x27_1002_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v_val_1009_);
lean_ctor_set(v___x_982_, 0, v_size_x27_1000_);
v___x_1011_ = v___x_982_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_size_x27_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_val_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v___x_1014_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v_buckets_x27_1002_);
lean_ctor_set(v___x_982_, 0, v_size_x27_1000_);
v___x_1014_ = v___x_982_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_size_x27_1000_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_buckets_x27_1002_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v___x_1016_; lean_object* v_buckets_x27_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_inc(v_bkt_997_);
v___x_1016_ = lean_box(0);
v_buckets_x27_1017_ = lean_array_uset(v_buckets_980_, v___x_996_, v___x_1016_);
v___x_1018_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_a_977_, v_b_978_, v_bkt_997_);
v___x_1019_ = lean_array_uset(v_buckets_x27_1017_, v___x_996_, v___x_1018_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_1019_);
v___x_1021_ = v___x_982_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_size_979_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(lean_object* v_a_1024_, lean_object* v_e_1025_, lean_object* v_fst_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = lean_st_ref_take(v_a_1024_);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v___x_1028_, v_e_1025_, v_fst_1026_);
v___x_1030_ = lean_st_ref_set(v_a_1024_, v___x_1029_);
v___x_1031_ = lean_box(0);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(lean_object* v_a_1032_, lean_object* v_e_1033_, lean_object* v_fst_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_1032_, v_e_1033_, v_fst_1034_);
lean_dec(v_a_1032_);
return v_res_1036_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = l_Lean_maxRecDepthErrorMessage;
v___x_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__3);
v___x_1045_ = l_Lean_MessageData_ofFormat(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__4);
v___x_1047_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__2));
v___x_1048_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(lean_object* v_ref_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___closed__5);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_ref_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(v_ref_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___y_1066_; lean_object* v_fileName_1083_; lean_object* v_fileMap_1084_; lean_object* v_options_1085_; lean_object* v_currRecDepth_1086_; lean_object* v_maxRecDepth_1087_; lean_object* v_ref_1088_; lean_object* v_currNamespace_1089_; lean_object* v_openDecls_1090_; lean_object* v_initHeartbeats_1091_; lean_object* v_maxHeartbeats_1092_; lean_object* v_quotContext_1093_; lean_object* v_currMacroScope_1094_; uint8_t v_diag_1095_; lean_object* v_cancelTk_x3f_1096_; uint8_t v_suppressElabErrors_1097_; lean_object* v_inheritedTraceOptions_1098_; uint8_t v___x_1099_; 
v_fileName_1083_ = lean_ctor_get(v___y_1062_, 0);
lean_inc_ref(v_fileName_1083_);
v_fileMap_1084_ = lean_ctor_get(v___y_1062_, 1);
lean_inc_ref(v_fileMap_1084_);
v_options_1085_ = lean_ctor_get(v___y_1062_, 2);
lean_inc_ref(v_options_1085_);
v_currRecDepth_1086_ = lean_ctor_get(v___y_1062_, 3);
lean_inc(v_currRecDepth_1086_);
v_maxRecDepth_1087_ = lean_ctor_get(v___y_1062_, 4);
lean_inc(v_maxRecDepth_1087_);
v_ref_1088_ = lean_ctor_get(v___y_1062_, 5);
lean_inc(v_ref_1088_);
v_currNamespace_1089_ = lean_ctor_get(v___y_1062_, 6);
lean_inc(v_currNamespace_1089_);
v_openDecls_1090_ = lean_ctor_get(v___y_1062_, 7);
lean_inc(v_openDecls_1090_);
v_initHeartbeats_1091_ = lean_ctor_get(v___y_1062_, 8);
lean_inc(v_initHeartbeats_1091_);
v_maxHeartbeats_1092_ = lean_ctor_get(v___y_1062_, 9);
lean_inc(v_maxHeartbeats_1092_);
v_quotContext_1093_ = lean_ctor_get(v___y_1062_, 10);
lean_inc(v_quotContext_1093_);
v_currMacroScope_1094_ = lean_ctor_get(v___y_1062_, 11);
lean_inc(v_currMacroScope_1094_);
v_diag_1095_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*14);
v_cancelTk_x3f_1096_ = lean_ctor_get(v___y_1062_, 12);
lean_inc(v_cancelTk_x3f_1096_);
v_suppressElabErrors_1097_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1098_ = lean_ctor_get(v___y_1062_, 13);
lean_inc_ref(v_inheritedTraceOptions_1098_);
lean_dec_ref(v___y_1062_);
v___x_1099_ = lean_nat_dec_eq(v_currRecDepth_1086_, v_maxRecDepth_1087_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_nat_add(v_currRecDepth_1086_, v___x_1100_);
lean_dec(v_currRecDepth_1086_);
v___x_1102_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1102_, 0, v_fileName_1083_);
lean_ctor_set(v___x_1102_, 1, v_fileMap_1084_);
lean_ctor_set(v___x_1102_, 2, v_options_1085_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
lean_ctor_set(v___x_1102_, 4, v_maxRecDepth_1087_);
lean_ctor_set(v___x_1102_, 5, v_ref_1088_);
lean_ctor_set(v___x_1102_, 6, v_currNamespace_1089_);
lean_ctor_set(v___x_1102_, 7, v_openDecls_1090_);
lean_ctor_set(v___x_1102_, 8, v_initHeartbeats_1091_);
lean_ctor_set(v___x_1102_, 9, v_maxHeartbeats_1092_);
lean_ctor_set(v___x_1102_, 10, v_quotContext_1093_);
lean_ctor_set(v___x_1102_, 11, v_currMacroScope_1094_);
lean_ctor_set(v___x_1102_, 12, v_cancelTk_x3f_1096_);
lean_ctor_set(v___x_1102_, 13, v_inheritedTraceOptions_1098_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*14, v_diag_1095_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*14 + 1, v_suppressElabErrors_1097_);
lean_inc(v___y_1063_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1058_);
v___x_1103_ = lean_apply_7(v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___x_1102_, v___y_1063_, lean_box(0));
v___y_1066_ = v___x_1103_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1104_; 
lean_dec_ref(v_inheritedTraceOptions_1098_);
lean_dec(v_cancelTk_x3f_1096_);
lean_dec(v_currMacroScope_1094_);
lean_dec(v_quotContext_1093_);
lean_dec(v_maxHeartbeats_1092_);
lean_dec(v_initHeartbeats_1091_);
lean_dec(v_openDecls_1090_);
lean_dec(v_currNamespace_1089_);
lean_dec(v_maxRecDepth_1087_);
lean_dec(v_currRecDepth_1086_);
lean_dec_ref(v_options_1085_);
lean_dec_ref(v_fileMap_1084_);
lean_dec_ref(v_fileName_1083_);
lean_dec(v___y_1059_);
lean_dec_ref(v_x_1057_);
v___x_1104_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(v_ref_1088_);
v___y_1066_ = v___x_1104_;
goto v___jp_1065_;
}
v___jp_1065_:
{
if (lean_obj_tag(v___y_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___y_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___y_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___y_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___y_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___y_1066_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___y_1066_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___y_1066_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___y_1066_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg___boxed(lean_object* v_x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1106_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(lean_object* v_a_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1115_) == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
else
{
lean_object* v_key_1117_; lean_object* v_value_1118_; lean_object* v_tail_1119_; uint8_t v___x_1120_; 
v_key_1117_ = lean_ctor_get(v_x_1115_, 0);
v_value_1118_ = lean_ctor_get(v_x_1115_, 1);
v_tail_1119_ = lean_ctor_get(v_x_1115_, 2);
v___x_1120_ = l_Lean_ExprStructEq_beq(v_key_1117_, v_a_1114_);
if (v___x_1120_ == 0)
{
v_x_1115_ = v_tail_1119_;
goto _start;
}
else
{
lean_object* v___x_1122_; 
lean_inc(v_value_1118_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_value_1118_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_1123_, v_x_1124_);
lean_dec(v_x_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(lean_object* v_m_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_buckets_1128_; lean_object* v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v_fold_1133_; uint64_t v___x_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_buckets_1128_ = lean_ctor_get(v_m_1126_, 1);
v___x_1129_ = lean_array_get_size(v_buckets_1128_);
v___x_1130_ = l_Lean_ExprStructEq_hash(v_a_1127_);
v___x_1131_ = 32ULL;
v___x_1132_ = lean_uint64_shift_right(v___x_1130_, v___x_1131_);
v_fold_1133_ = lean_uint64_xor(v___x_1130_, v___x_1132_);
v___x_1134_ = 16ULL;
v___x_1135_ = lean_uint64_shift_right(v_fold_1133_, v___x_1134_);
v___x_1136_ = lean_uint64_xor(v_fold_1133_, v___x_1135_);
v___x_1137_ = lean_uint64_to_usize(v___x_1136_);
v___x_1138_ = lean_usize_of_nat(v___x_1129_);
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_sub(v___x_1138_, v___x_1139_);
v___x_1141_ = lean_usize_land(v___x_1137_, v___x_1140_);
v___x_1142_ = lean_array_uget_borrowed(v_buckets_1128_, v___x_1141_);
v___x_1143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_1127_, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_1144_, v_a_1145_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_m_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_object* v_00_u03b1_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_apply_1(v_x_1148_, lean_box(0));
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___y_1149_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_1158_, v_x_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(lean_object* v_fvars_1169_, lean_object* v_pre_1170_, lean_object* v_post_1171_, uint8_t v_usedLetOnly_1172_, uint8_t v_skipConstInApp_1173_, uint8_t v_skipInstances_1174_, lean_object* v_body_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_array_push(v_fvars_1169_, v_x_1176_);
v___x_1185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1170_, v_post_1171_, v_usedLetOnly_1172_, v_skipConstInApp_1173_, v_skipInstances_1174_, v___x_1184_, v_body_1175_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(lean_object* v_fvars_1186_, lean_object* v_pre_1187_, lean_object* v_post_1188_, lean_object* v_usedLetOnly_1189_, lean_object* v_skipConstInApp_1190_, lean_object* v_skipInstances_1191_, lean_object* v_body_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v_usedLetOnly_boxed_1201_; uint8_t v_skipConstInApp_boxed_1202_; uint8_t v_skipInstances_boxed_1203_; lean_object* v_res_1204_; 
v_usedLetOnly_boxed_1201_ = lean_unbox(v_usedLetOnly_1189_);
v_skipConstInApp_boxed_1202_ = lean_unbox(v_skipConstInApp_1190_);
v_skipInstances_boxed_1203_ = lean_unbox(v_skipInstances_1191_);
v_res_1204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_1186_, v_pre_1187_, v_post_1188_, v_usedLetOnly_boxed_1201_, v_skipConstInApp_boxed_1202_, v_skipInstances_boxed_1203_, v_body_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1194_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(lean_object* v_pre_1205_, lean_object* v_post_1206_, uint8_t v_usedLetOnly_1207_, uint8_t v_skipConstInApp_1208_, uint8_t v_skipInstances_1209_, lean_object* v_e_1210_, lean_object* v_a_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
lean_inc_ref(v_post_1206_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc_ref(v_e_1210_);
v___x_1218_ = lean_apply_7(v_post_1206_, v_e_1210_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1250_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1249_; 
v_fst_1223_ = lean_ctor_get(v_a_1219_, 0);
v_snd_1224_ = lean_ctor_get(v_a_1219_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1226_ = v_a_1219_;
v_isShared_1227_ = v_isSharedCheck_1249_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_inc(v_fst_1223_);
lean_dec(v_a_1219_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1249_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___y_1229_; 
switch(lean_obj_tag(v_fst_1223_))
{
case 0:
{
lean_object* v_e_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
lean_del_object(v___x_1226_);
lean_del_object(v___x_1221_);
lean_dec_ref(v_e_1210_);
lean_dec_ref(v_post_1206_);
lean_dec_ref(v_pre_1205_);
v_e_1236_ = lean_ctor_get(v_fst_1223_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_fst_1223_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1238_ = v_fst_1223_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_e_1236_);
lean_dec(v_fst_1223_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_e_1236_);
lean_ctor_set(v___x_1240_, 1, v_snd_1224_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
case 1:
{
lean_object* v_e_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1226_);
lean_del_object(v___x_1221_);
lean_dec_ref(v_e_1210_);
v_e_1245_ = lean_ctor_get(v_fst_1223_, 0);
lean_inc_ref(v_e_1245_);
lean_dec_ref(v_fst_1223_);
v___x_1246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1205_, v_post_1206_, v_usedLetOnly_1207_, v_skipConstInApp_1208_, v_skipInstances_1209_, v_e_1245_, v_a_1211_, v_snd_1224_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1246_;
}
default: 
{
lean_object* v_e_x3f_1247_; 
lean_dec_ref(v_post_1206_);
lean_dec_ref(v_pre_1205_);
v_e_x3f_1247_ = lean_ctor_get(v_fst_1223_, 0);
lean_inc(v_e_x3f_1247_);
lean_dec_ref(v_fst_1223_);
if (lean_obj_tag(v_e_x3f_1247_) == 0)
{
v___y_1229_ = v_e_1210_;
goto v___jp_1228_;
}
else
{
lean_object* v_val_1248_; 
lean_dec_ref(v_e_1210_);
v_val_1248_ = lean_ctor_get(v_e_x3f_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref(v_e_x3f_1247_);
v___y_1229_ = v_val_1248_;
goto v___jp_1228_;
}
}
}
v___jp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___y_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___y_1229_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_snd_1224_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1231_);
v___x_1233_ = v___x_1221_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
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
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_e_1210_);
lean_dec_ref(v_post_1206_);
lean_dec_ref(v_pre_1205_);
v_a_1251_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1218_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1218_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(lean_object* v_pre_1259_, lean_object* v_post_1260_, uint8_t v_usedLetOnly_1261_, uint8_t v_skipConstInApp_1262_, uint8_t v_skipInstances_1263_, lean_object* v_fvars_1264_, lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
if (lean_obj_tag(v_e_1265_) == 6)
{
lean_object* v_binderName_1273_; lean_object* v_binderType_1274_; lean_object* v_body_1275_; uint8_t v_binderInfo_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_binderName_1273_ = lean_ctor_get(v_e_1265_, 0);
lean_inc(v_binderName_1273_);
v_binderType_1274_ = lean_ctor_get(v_e_1265_, 1);
lean_inc_ref(v_binderType_1274_);
v_body_1275_ = lean_ctor_get(v_e_1265_, 2);
lean_inc_ref(v_body_1275_);
v_binderInfo_1276_ = lean_ctor_get_uint8(v_e_1265_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1265_);
v___x_1277_ = lean_expr_instantiate_rev(v_binderType_1274_, v_fvars_1264_);
lean_dec_ref(v_binderType_1274_);
lean_inc_ref(v_post_1260_);
lean_inc_ref(v_pre_1259_);
v___x_1278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1259_, v_post_1260_, v_usedLetOnly_1261_, v_skipConstInApp_1262_, v_skipInstances_1263_, v___x_1277_, v_a_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v_fst_1280_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v_a_1279_, 1);
lean_inc(v_snd_1281_);
lean_dec(v_a_1279_);
v___x_1282_ = lean_box(v_usedLetOnly_1261_);
v___x_1283_ = lean_box(v_skipConstInApp_1262_);
v___x_1284_ = lean_box(v_skipInstances_1263_);
v___f_1285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1285_, 0, v_fvars_1264_);
lean_closure_set(v___f_1285_, 1, v_pre_1259_);
lean_closure_set(v___f_1285_, 2, v_post_1260_);
lean_closure_set(v___f_1285_, 3, v___x_1282_);
lean_closure_set(v___f_1285_, 4, v___x_1283_);
lean_closure_set(v___f_1285_, 5, v___x_1284_);
lean_closure_set(v___f_1285_, 6, v_body_1275_);
v___x_1286_ = 0;
v___x_1287_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_binderName_1273_, v_binderInfo_1276_, v_fst_1280_, v___f_1285_, v___x_1286_, v_a_1266_, v_snd_1281_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1287_;
}
else
{
lean_dec_ref(v_body_1275_);
lean_dec(v_binderName_1273_);
lean_dec_ref(v_fvars_1264_);
lean_dec_ref(v_post_1260_);
lean_dec_ref(v_pre_1259_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_expr_instantiate_rev(v_e_1265_, v_fvars_1264_);
lean_dec_ref(v_e_1265_);
lean_inc_ref(v_post_1260_);
lean_inc_ref(v_pre_1259_);
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1259_, v_post_1260_, v_usedLetOnly_1261_, v_skipConstInApp_1262_, v_skipInstances_1263_, v___x_1288_, v_a_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; uint8_t v___x_1293_; uint8_t v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1289_);
v_fst_1291_ = lean_ctor_get(v_a_1290_, 0);
lean_inc(v_fst_1291_);
v_snd_1292_ = lean_ctor_get(v_a_1290_, 1);
lean_inc(v_snd_1292_);
lean_dec(v_a_1290_);
v___x_1293_ = 0;
v___x_1294_ = 1;
v___x_1295_ = 1;
v___x_1296_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1264_, v_fst_1291_, v___x_1293_, v_usedLetOnly_1261_, v___x_1293_, v___x_1294_, v___x_1295_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec_ref(v_fvars_1264_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1259_, v_post_1260_, v_usedLetOnly_1261_, v_skipConstInApp_1262_, v_skipInstances_1263_, v_a_1297_, v_a_1266_, v_snd_1292_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1298_;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_snd_1292_);
lean_dec_ref(v_post_1260_);
lean_dec_ref(v_pre_1259_);
v_a_1299_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1296_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1296_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1264_);
lean_dec_ref(v_post_1260_);
lean_dec_ref(v_pre_1259_);
return v___x_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(lean_object* v_fvars_1307_, lean_object* v_pre_1308_, lean_object* v_post_1309_, uint8_t v_usedLetOnly_1310_, uint8_t v_skipConstInApp_1311_, uint8_t v_skipInstances_1312_, lean_object* v_body_1313_, lean_object* v_x_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_array_push(v_fvars_1307_, v_x_1314_);
v___x_1323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1308_, v_post_1309_, v_usedLetOnly_1310_, v_skipConstInApp_1311_, v_skipInstances_1312_, v___x_1322_, v_body_1313_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed(lean_object* v_fvars_1324_, lean_object* v_pre_1325_, lean_object* v_post_1326_, lean_object* v_usedLetOnly_1327_, lean_object* v_skipConstInApp_1328_, lean_object* v_skipInstances_1329_, lean_object* v_body_1330_, lean_object* v_x_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_usedLetOnly_boxed_1339_; uint8_t v_skipConstInApp_boxed_1340_; uint8_t v_skipInstances_boxed_1341_; lean_object* v_res_1342_; 
v_usedLetOnly_boxed_1339_ = lean_unbox(v_usedLetOnly_1327_);
v_skipConstInApp_boxed_1340_ = lean_unbox(v_skipConstInApp_1328_);
v_skipInstances_boxed_1341_ = lean_unbox(v_skipInstances_1329_);
v_res_1342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0(v_fvars_1324_, v_pre_1325_, v_post_1326_, v_usedLetOnly_boxed_1339_, v_skipConstInApp_boxed_1340_, v_skipInstances_boxed_1341_, v_body_1330_, v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1332_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(lean_object* v_pre_1343_, lean_object* v_post_1344_, uint8_t v_usedLetOnly_1345_, uint8_t v_skipConstInApp_1346_, uint8_t v_skipInstances_1347_, lean_object* v_fvars_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
if (lean_obj_tag(v_e_1349_) == 8)
{
lean_object* v_declName_1357_; lean_object* v_type_1358_; lean_object* v_value_1359_; lean_object* v_body_1360_; uint8_t v_nondep_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_declName_1357_ = lean_ctor_get(v_e_1349_, 0);
lean_inc(v_declName_1357_);
v_type_1358_ = lean_ctor_get(v_e_1349_, 1);
lean_inc_ref(v_type_1358_);
v_value_1359_ = lean_ctor_get(v_e_1349_, 2);
lean_inc_ref(v_value_1359_);
v_body_1360_ = lean_ctor_get(v_e_1349_, 3);
lean_inc_ref(v_body_1360_);
v_nondep_1361_ = lean_ctor_get_uint8(v_e_1349_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1349_);
v___x_1362_ = lean_expr_instantiate_rev(v_type_1358_, v_fvars_1348_);
lean_dec_ref(v_type_1358_);
lean_inc_ref(v_post_1344_);
lean_inc_ref(v_pre_1343_);
v___x_1363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1343_, v_post_1344_, v_usedLetOnly_1345_, v_skipConstInApp_1346_, v_skipInstances_1347_, v___x_1362_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v_fst_1365_ = lean_ctor_get(v_a_1364_, 0);
lean_inc(v_fst_1365_);
v_snd_1366_ = lean_ctor_get(v_a_1364_, 1);
lean_inc(v_snd_1366_);
lean_dec(v_a_1364_);
v___x_1367_ = lean_expr_instantiate_rev(v_value_1359_, v_fvars_1348_);
lean_dec_ref(v_value_1359_);
lean_inc_ref(v_post_1344_);
lean_inc_ref(v_pre_1343_);
v___x_1368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1343_, v_post_1344_, v_usedLetOnly_1345_, v_skipConstInApp_1346_, v_skipInstances_1347_, v___x_1367_, v_a_1350_, v_snd_1366_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1368_);
v_fst_1370_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_fst_1370_);
v_snd_1371_ = lean_ctor_get(v_a_1369_, 1);
lean_inc(v_snd_1371_);
lean_dec(v_a_1369_);
v___x_1372_ = lean_box(v_usedLetOnly_1345_);
v___x_1373_ = lean_box(v_skipConstInApp_1346_);
v___x_1374_ = lean_box(v_skipInstances_1347_);
v___f_1375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1375_, 0, v_fvars_1348_);
lean_closure_set(v___f_1375_, 1, v_pre_1343_);
lean_closure_set(v___f_1375_, 2, v_post_1344_);
lean_closure_set(v___f_1375_, 3, v___x_1372_);
lean_closure_set(v___f_1375_, 4, v___x_1373_);
lean_closure_set(v___f_1375_, 5, v___x_1374_);
lean_closure_set(v___f_1375_, 6, v_body_1360_);
v___x_1376_ = 0;
v___x_1377_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(v_declName_1357_, v_fst_1365_, v_fst_1370_, v___f_1375_, v_nondep_1361_, v___x_1376_, v_a_1350_, v_snd_1371_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1377_;
}
else
{
lean_dec(v_fst_1365_);
lean_dec_ref(v_body_1360_);
lean_dec(v_declName_1357_);
lean_dec_ref(v_fvars_1348_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
return v___x_1368_;
}
}
else
{
lean_dec_ref(v_body_1360_);
lean_dec_ref(v_value_1359_);
lean_dec(v_declName_1357_);
lean_dec_ref(v_fvars_1348_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_expr_instantiate_rev(v_e_1349_, v_fvars_1348_);
lean_dec_ref(v_e_1349_);
lean_inc_ref(v_post_1344_);
lean_inc_ref(v_pre_1343_);
v___x_1379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1343_, v_post_1344_, v_usedLetOnly_1345_, v_skipConstInApp_1346_, v_skipInstances_1347_, v___x_1378_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_fst_1381_; lean_object* v_snd_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v_fst_1381_ = lean_ctor_get(v_a_1380_, 0);
lean_inc(v_fst_1381_);
v_snd_1382_ = lean_ctor_get(v_a_1380_, 1);
lean_inc(v_snd_1382_);
lean_dec(v_a_1380_);
v___x_1383_ = 0;
v___x_1384_ = 1;
v___x_1385_ = l_Lean_Meta_mkLetFVars(v_fvars_1348_, v_fst_1381_, v_usedLetOnly_1345_, v___x_1383_, v___x_1384_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec_ref(v_fvars_1348_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1343_, v_post_1344_, v_usedLetOnly_1345_, v_skipConstInApp_1346_, v_skipInstances_1347_, v_a_1386_, v_a_1350_, v_snd_1382_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_snd_1382_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
v_a_1388_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1385_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1385_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1348_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(lean_object* v_pre_1396_, lean_object* v_post_1397_, uint8_t v_usedLetOnly_1398_, uint8_t v_skipConstInApp_1399_, uint8_t v_skipInstances_1400_, size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_bs_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_bs_1403_);
lean_ctor_set(v___x_1412_, 1, v___y_1405_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
else
{
lean_object* v_v_1414_; lean_object* v___x_1415_; 
v_v_1414_ = lean_array_uget_borrowed(v_bs_1403_, v_i_1402_);
lean_inc(v_v_1414_);
lean_inc_ref(v_post_1397_);
lean_inc_ref(v_pre_1396_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1396_, v_post_1397_, v_usedLetOnly_1398_, v_skipConstInApp_1399_, v_skipInstances_1400_, v_v_1414_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1419_; lean_object* v_bs_x27_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v_fst_1417_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_fst_1417_);
v_snd_1418_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_snd_1418_);
lean_dec(v_a_1416_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v_bs_x27_1420_ = lean_array_uset(v_bs_1403_, v_i_1402_, v___x_1419_);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1402_, v___x_1421_);
v___x_1423_ = lean_array_uset(v_bs_x27_1420_, v_i_1402_, v_fst_1417_);
v_i_1402_ = v___x_1422_;
v_bs_1403_ = v___x_1423_;
v___y_1405_ = v_snd_1418_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_bs_1403_);
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(lean_object* v_pre_1433_, lean_object* v_post_1434_, uint8_t v_usedLetOnly_1435_, uint8_t v_skipConstInApp_1436_, uint8_t v_skipInstances_1437_, lean_object* v___x_1438_, lean_object* v___y_1439_, lean_object* v_b_1440_, lean_object* v_a_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1433_, v_post_1434_, v_usedLetOnly_1435_, v_skipConstInApp_1436_, v_skipInstances_1437_, v___x_1438_, v___y_1439_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1467_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1466_; 
v_fst_1453_ = lean_ctor_get(v_a_1449_, 0);
v_snd_1454_ = lean_ctor_get(v_a_1449_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_a_1449_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1456_ = v_a_1449_;
v_isShared_1457_ = v_isSharedCheck_1466_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_snd_1454_);
lean_inc(v_fst_1453_);
lean_dec(v_a_1449_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1466_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_array_fset(v_b_1440_, v_a_1441_, v_fst_1453_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_snd_1454_);
v___x_1461_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1461_);
v___x_1463_ = v___x_1451_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_b_1440_);
v_a_1468_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1448_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1448_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed(lean_object* v_pre_1476_, lean_object* v_post_1477_, lean_object* v_usedLetOnly_1478_, lean_object* v_skipConstInApp_1479_, lean_object* v_skipInstances_1480_, lean_object* v___x_1481_, lean_object* v___y_1482_, lean_object* v_b_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_usedLetOnly_boxed_1491_; uint8_t v_skipConstInApp_boxed_1492_; uint8_t v_skipInstances_boxed_1493_; lean_object* v_res_1494_; 
v_usedLetOnly_boxed_1491_ = lean_unbox(v_usedLetOnly_1478_);
v_skipConstInApp_boxed_1492_ = lean_unbox(v_skipConstInApp_1479_);
v_skipInstances_boxed_1493_ = lean_unbox(v_skipInstances_1480_);
v_res_1494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0(v_pre_1476_, v_post_1477_, v_usedLetOnly_boxed_1491_, v_skipConstInApp_boxed_1492_, v_skipInstances_boxed_1493_, v___x_1481_, v___y_1482_, v_b_1483_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v_a_1484_);
lean_dec(v___y_1482_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_1495_, lean_object* v___x_1496_, lean_object* v_pre_1497_, lean_object* v_post_1498_, uint8_t v_usedLetOnly_1499_, uint8_t v_skipConstInApp_1500_, uint8_t v_skipInstances_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___y_1512_; uint8_t v___x_1546_; 
v___x_1546_ = lean_nat_dec_lt(v_a_1502_, v_upperBound_1495_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_post_1498_);
lean_dec_ref(v_pre_1497_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_b_1503_);
lean_ctor_set(v___x_1547_, 1, v___y_1505_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_array_fget_borrowed(v_b_1503_, v_a_1502_);
v___x_1550_ = lean_array_get_size(v___x_1496_);
v___x_1551_ = lean_nat_dec_lt(v_a_1502_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___f_1555_; 
lean_inc(v___x_1549_);
v___x_1552_ = lean_box(v_usedLetOnly_1499_);
v___x_1553_ = lean_box(v_skipConstInApp_1500_);
v___x_1554_ = lean_box(v_skipInstances_1501_);
lean_inc(v_a_1502_);
lean_inc(v___y_1504_);
lean_inc_ref(v_post_1498_);
lean_inc_ref(v_pre_1497_);
v___f_1555_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1555_, 0, v_pre_1497_);
lean_closure_set(v___f_1555_, 1, v_post_1498_);
lean_closure_set(v___f_1555_, 2, v___x_1552_);
lean_closure_set(v___f_1555_, 3, v___x_1553_);
lean_closure_set(v___f_1555_, 4, v___x_1554_);
lean_closure_set(v___f_1555_, 5, v___x_1549_);
lean_closure_set(v___f_1555_, 6, v___y_1504_);
lean_closure_set(v___f_1555_, 7, v_b_1503_);
lean_closure_set(v___f_1555_, 8, v_a_1502_);
v___y_1512_ = v___f_1555_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1556_; uint8_t v_isInstance_1557_; 
v___x_1556_ = lean_array_fget_borrowed(v___x_1496_, v_a_1502_);
v_isInstance_1557_ = lean_ctor_get_uint8(v___x_1556_, sizeof(void*)*1 + 4);
if (v_isInstance_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; 
lean_inc(v___x_1549_);
v___x_1558_ = lean_box(v_usedLetOnly_1499_);
v___x_1559_ = lean_box(v_skipConstInApp_1500_);
v___x_1560_ = lean_box(v_skipInstances_1501_);
lean_inc(v_a_1502_);
lean_inc(v___y_1504_);
lean_inc_ref(v_post_1498_);
lean_inc_ref(v_pre_1497_);
v___f_1561_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1561_, 0, v_pre_1497_);
lean_closure_set(v___f_1561_, 1, v_post_1498_);
lean_closure_set(v___f_1561_, 2, v___x_1558_);
lean_closure_set(v___f_1561_, 3, v___x_1559_);
lean_closure_set(v___f_1561_, 4, v___x_1560_);
lean_closure_set(v___f_1561_, 5, v___x_1549_);
lean_closure_set(v___f_1561_, 6, v___y_1504_);
lean_closure_set(v___f_1561_, 7, v_b_1503_);
lean_closure_set(v___f_1561_, 8, v_a_1502_);
v___y_1512_ = v___f_1561_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1562_; lean_object* v___f_1563_; 
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_b_1503_);
v___f_1563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_1563_, 0, v___x_1562_);
v___y_1512_ = v___f_1563_;
goto v___jp_1511_;
}
}
}
v___jp_1511_:
{
lean_object* v___x_1513_; 
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
v___x_1513_ = lean_apply_6(v___y_1512_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1537_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_fst_1518_; 
v_fst_1518_ = lean_ctor_get(v_a_1514_, 0);
lean_inc(v_fst_1518_);
if (lean_obj_tag(v_fst_1518_) == 0)
{
lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_post_1498_);
lean_dec_ref(v_pre_1497_);
v_snd_1519_ = lean_ctor_get(v_a_1514_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_a_1514_, 0);
lean_dec(v_unused_1531_);
v___x_1521_ = v_a_1514_;
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_dec(v_a_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v_a_1523_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v_fst_1518_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v_fst_1518_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_a_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_snd_1519_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1525_);
v___x_1527_ = v___x_1516_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_snd_1532_; lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_del_object(v___x_1516_);
v_snd_1532_ = lean_ctor_get(v_a_1514_, 1);
lean_inc(v_snd_1532_);
lean_dec(v_a_1514_);
v_a_1533_ = lean_ctor_get(v_fst_1518_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v_fst_1518_);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v_a_1502_, v___x_1534_);
lean_dec(v_a_1502_);
v_a_1502_ = v___x_1535_;
v_b_1503_ = v_a_1533_;
v___y_1505_ = v_snd_1532_;
goto _start;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_post_1498_);
lean_dec_ref(v_pre_1497_);
v_a_1538_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1513_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1513_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(uint8_t v_skipInstances_1564_, lean_object* v_pre_1565_, lean_object* v_post_1566_, uint8_t v_usedLetOnly_1567_, uint8_t v_skipConstInApp_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_f_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; 
if (lean_obj_tag(v_x_1569_) == 5)
{
lean_object* v_fn_1635_; lean_object* v_arg_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_fn_1635_ = lean_ctor_get(v_x_1569_, 0);
lean_inc_ref(v_fn_1635_);
v_arg_1636_ = lean_ctor_get(v_x_1569_, 1);
lean_inc_ref(v_arg_1636_);
lean_dec_ref(v_x_1569_);
v___x_1637_ = lean_array_set(v_x_1570_, v_x_1571_, v_arg_1636_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_sub(v_x_1571_, v___x_1638_);
lean_dec(v_x_1571_);
v_x_1569_ = v_fn_1635_;
v_x_1570_ = v___x_1637_;
v_x_1571_ = v___x_1639_;
goto _start;
}
else
{
lean_dec(v_x_1571_);
if (v_skipConstInApp_1568_ == 0)
{
goto v___jp_1630_;
}
else
{
uint8_t v___x_1641_; 
v___x_1641_ = l_Lean_Expr_isConst(v_x_1569_);
if (v___x_1641_ == 0)
{
goto v___jp_1630_;
}
else
{
v_f_1580_ = v_x_1569_;
v___y_1581_ = v___y_1572_;
v___y_1582_ = v___y_1573_;
v___y_1583_ = v___y_1574_;
v___y_1584_ = v___y_1575_;
v___y_1585_ = v___y_1576_;
v___y_1586_ = v___y_1577_;
goto v___jp_1579_;
}
}
}
v___jp_1579_:
{
if (v_skipInstances_1564_ == 0)
{
size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_sz_1587_ = lean_array_size(v_x_1570_);
v___x_1588_ = ((size_t)0ULL);
lean_inc_ref(v_post_1566_);
lean_inc_ref(v_pre_1565_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1565_, v_post_1566_, v_usedLetOnly_1567_, v_skipConstInApp_1568_, v_skipInstances_1564_, v_sz_1587_, v___x_1588_, v_x_1570_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_fst_1591_; lean_object* v_snd_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v_fst_1591_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_fst_1591_);
v_snd_1592_ = lean_ctor_get(v_a_1590_, 1);
lean_inc(v_snd_1592_);
lean_dec(v_a_1590_);
v___x_1593_ = l_Lean_mkAppN(v_f_1580_, v_fst_1591_);
lean_dec(v_fst_1591_);
v___x_1594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1565_, v_post_1566_, v_usedLetOnly_1567_, v_skipConstInApp_1568_, v_skipInstances_1564_, v___x_1593_, v___y_1581_, v_snd_1592_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_f_1580_);
lean_dec_ref(v_post_1566_);
lean_dec_ref(v_pre_1565_);
v_a_1595_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1589_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1589_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_array_get_size(v_x_1570_);
lean_inc_ref(v_f_1580_);
v___x_1604_ = l_Lean_Meta_getFunInfoNArgs(v_f_1580_, v___x_1603_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_paramInfo_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v_paramInfo_1606_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_ref(v_paramInfo_1606_);
lean_dec(v_a_1605_);
v___x_1607_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1566_);
lean_inc_ref(v_pre_1565_);
v___x_1608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v___x_1603_, v_paramInfo_1606_, v_pre_1565_, v_post_1566_, v_usedLetOnly_1567_, v_skipConstInApp_1568_, v_skipInstances_1564_, v___x_1607_, v_x_1570_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v_paramInfo_1606_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v_fst_1610_; lean_object* v_snd_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1608_);
v_fst_1610_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_fst_1610_);
v_snd_1611_ = lean_ctor_get(v_a_1609_, 1);
lean_inc(v_snd_1611_);
lean_dec(v_a_1609_);
v___x_1612_ = l_Lean_mkAppN(v_f_1580_, v_fst_1610_);
lean_dec(v_fst_1610_);
v___x_1613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1565_, v_post_1566_, v_usedLetOnly_1567_, v_skipConstInApp_1568_, v_skipInstances_1564_, v___x_1612_, v___y_1581_, v_snd_1611_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1613_;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v_f_1580_);
lean_dec_ref(v_post_1566_);
lean_dec_ref(v_pre_1565_);
v_a_1614_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1608_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1608_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v___y_1582_);
lean_dec_ref(v_f_1580_);
lean_dec_ref(v_x_1570_);
lean_dec_ref(v_post_1566_);
lean_dec_ref(v_pre_1565_);
v_a_1622_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1604_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1604_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
v___jp_1630_:
{
lean_object* v___x_1631_; 
lean_inc_ref(v_post_1566_);
lean_inc_ref(v_pre_1565_);
v___x_1631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1565_, v_post_1566_, v_usedLetOnly_1567_, v_skipConstInApp_1568_, v_skipInstances_1564_, v_x_1569_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v_fst_1633_; lean_object* v_snd_1634_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
v_fst_1633_ = lean_ctor_get(v_a_1632_, 0);
lean_inc(v_fst_1633_);
v_snd_1634_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_snd_1634_);
lean_dec(v_a_1632_);
v_f_1580_ = v_fst_1633_;
v___y_1581_ = v___y_1572_;
v___y_1582_ = v_snd_1634_;
v___y_1583_ = v___y_1574_;
v___y_1584_ = v___y_1575_;
v___y_1585_ = v___y_1576_;
v___y_1586_ = v___y_1577_;
goto v___jp_1579_;
}
else
{
lean_dec_ref(v_x_1570_);
lean_dec_ref(v_post_1566_);
lean_dec_ref(v_pre_1565_);
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(lean_object* v_pre_1642_, lean_object* v_e_1643_, lean_object* v_post_1644_, uint8_t v_usedLetOnly_1645_, uint8_t v_skipConstInApp_1646_, uint8_t v_skipInstances_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
lean_inc_ref(v_pre_1642_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc_ref(v_e_1643_);
v___x_1655_ = lean_apply_7(v_pre_1642_, v_e_1643_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, lean_box(0));
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1717_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1717_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1717_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1716_; 
v_fst_1660_ = lean_ctor_get(v_a_1656_, 0);
v_snd_1661_ = lean_ctor_get(v_a_1656_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1663_ = v_a_1656_;
v_isShared_1664_ = v_isSharedCheck_1716_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_inc(v_fst_1660_);
lean_dec(v_a_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1716_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___y_1666_; 
switch(lean_obj_tag(v_fst_1660_))
{
case 0:
{
lean_object* v_e_1705_; lean_object* v___x_1707_; 
lean_dec_ref(v_post_1644_);
lean_dec_ref(v_e_1643_);
lean_dec_ref(v_pre_1642_);
v_e_1705_ = lean_ctor_get(v_fst_1660_, 0);
lean_inc_ref(v_e_1705_);
lean_dec_ref(v_fst_1660_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v_e_1705_);
v___x_1707_ = v___x_1663_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_e_1705_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_snd_1661_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1707_);
v___x_1709_ = v___x_1658_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
case 1:
{
lean_object* v_e_1712_; lean_object* v___x_1713_; 
lean_del_object(v___x_1663_);
lean_del_object(v___x_1658_);
lean_dec_ref(v_e_1643_);
v_e_1712_ = lean_ctor_get(v_fst_1660_, 0);
lean_inc_ref(v_e_1712_);
lean_dec_ref(v_fst_1660_);
v___x_1713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v_e_1712_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1713_;
}
default: 
{
lean_object* v_e_x3f_1714_; 
lean_del_object(v___x_1663_);
lean_del_object(v___x_1658_);
v_e_x3f_1714_ = lean_ctor_get(v_fst_1660_, 0);
lean_inc(v_e_x3f_1714_);
lean_dec_ref(v_fst_1660_);
if (lean_obj_tag(v_e_x3f_1714_) == 0)
{
v___y_1666_ = v_e_1643_;
goto v___jp_1665_;
}
else
{
lean_object* v_val_1715_; 
lean_dec_ref(v_e_1643_);
v_val_1715_ = lean_ctor_get(v_e_x3f_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref(v_e_x3f_1714_);
v___y_1666_ = v_val_1715_;
goto v___jp_1665_;
}
}
}
v___jp_1665_:
{
switch(lean_obj_tag(v___y_1666_))
{
case 7:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___x_1667_, v___y_1666_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1668_;
}
case 6:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___x_1669_, v___y_1666_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1670_;
}
case 8:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0));
v___x_1672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___x_1671_, v___y_1666_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1672_;
}
case 5:
{
lean_object* v_dummy_1673_; lean_object* v_nargs_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_dummy_1673_ = lean_obj_once(&l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0, &l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once, _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
v_nargs_1674_ = l_Lean_Expr_getAppNumArgs(v___y_1666_);
lean_inc(v_nargs_1674_);
v___x_1675_ = lean_mk_array(v_nargs_1674_, v_dummy_1673_);
v___x_1676_ = lean_unsigned_to_nat(1u);
v___x_1677_ = lean_nat_sub(v_nargs_1674_, v___x_1676_);
lean_dec(v_nargs_1674_);
v___x_1678_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_1647_, v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v___y_1666_, v___x_1675_, v___x_1677_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1678_;
}
case 10:
{
lean_object* v_data_1679_; lean_object* v_expr_1680_; lean_object* v___x_1681_; 
v_data_1679_ = lean_ctor_get(v___y_1666_, 0);
v_expr_1680_ = lean_ctor_get(v___y_1666_, 1);
lean_inc_ref(v_expr_1680_);
lean_inc_ref(v_post_1644_);
lean_inc_ref(v_pre_1642_);
v___x_1681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v_expr_1680_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_fst_1683_; lean_object* v_snd_1684_; size_t v___x_1685_; size_t v___x_1686_; uint8_t v___x_1687_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v_fst_1683_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v_fst_1683_);
v_snd_1684_ = lean_ctor_get(v_a_1682_, 1);
lean_inc(v_snd_1684_);
lean_dec(v_a_1682_);
v___x_1685_ = lean_ptr_addr(v_expr_1680_);
v___x_1686_ = lean_ptr_addr(v_fst_1683_);
v___x_1687_ = lean_usize_dec_eq(v___x_1685_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_inc(v_data_1679_);
lean_dec_ref(v___y_1666_);
v___x_1688_ = l_Lean_Expr_mdata___override(v_data_1679_, v_fst_1683_);
v___x_1689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___x_1688_, v___y_1648_, v_snd_1684_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; 
lean_dec(v_fst_1683_);
v___x_1690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___y_1666_, v___y_1648_, v_snd_1684_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1690_;
}
}
else
{
lean_dec_ref(v___y_1666_);
lean_dec_ref(v_post_1644_);
lean_dec_ref(v_pre_1642_);
return v___x_1681_;
}
}
case 11:
{
lean_object* v_typeName_1691_; lean_object* v_idx_1692_; lean_object* v_struct_1693_; lean_object* v___x_1694_; 
v_typeName_1691_ = lean_ctor_get(v___y_1666_, 0);
v_idx_1692_ = lean_ctor_get(v___y_1666_, 1);
v_struct_1693_ = lean_ctor_get(v___y_1666_, 2);
lean_inc_ref(v_struct_1693_);
lean_inc_ref(v_post_1644_);
lean_inc_ref(v_pre_1642_);
v___x_1694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v_struct_1693_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; size_t v___x_1698_; size_t v___x_1699_; uint8_t v___x_1700_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v_fst_1696_ = lean_ctor_get(v_a_1695_, 0);
lean_inc(v_fst_1696_);
v_snd_1697_ = lean_ctor_get(v_a_1695_, 1);
lean_inc(v_snd_1697_);
lean_dec(v_a_1695_);
v___x_1698_ = lean_ptr_addr(v_struct_1693_);
v___x_1699_ = lean_ptr_addr(v_fst_1696_);
v___x_1700_ = lean_usize_dec_eq(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_inc(v_idx_1692_);
lean_inc(v_typeName_1691_);
lean_dec_ref(v___y_1666_);
v___x_1701_ = l_Lean_Expr_proj___override(v_typeName_1691_, v_idx_1692_, v_fst_1696_);
v___x_1702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___x_1701_, v___y_1648_, v_snd_1697_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_fst_1696_);
v___x_1703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___y_1666_, v___y_1648_, v_snd_1697_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1703_;
}
}
else
{
lean_dec_ref(v___y_1666_);
lean_dec_ref(v_post_1644_);
lean_dec_ref(v_pre_1642_);
return v___x_1694_;
}
}
default: 
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1642_, v_post_1644_, v_usedLetOnly_1645_, v_skipConstInApp_1646_, v_skipInstances_1647_, v___y_1666_, v___y_1648_, v_snd_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1704_;
}
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_post_1644_);
lean_dec_ref(v_e_1643_);
lean_dec_ref(v_pre_1642_);
v_a_1718_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1655_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1655_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(lean_object* v_pre_1726_, lean_object* v_e_1727_, lean_object* v_post_1728_, lean_object* v_usedLetOnly_1729_, lean_object* v_skipConstInApp_1730_, lean_object* v_skipInstances_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v_usedLetOnly_boxed_1739_; uint8_t v_skipConstInApp_boxed_1740_; uint8_t v_skipInstances_boxed_1741_; lean_object* v_res_1742_; 
v_usedLetOnly_boxed_1739_ = lean_unbox(v_usedLetOnly_1729_);
v_skipConstInApp_boxed_1740_ = lean_unbox(v_skipConstInApp_1730_);
v_skipInstances_boxed_1741_ = lean_unbox(v_skipInstances_1731_);
v_res_1742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v_pre_1726_, v_e_1727_, v_post_1728_, v_usedLetOnly_boxed_1739_, v_skipConstInApp_boxed_1740_, v_skipInstances_boxed_1741_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1732_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(lean_object* v_pre_1743_, lean_object* v_post_1744_, uint8_t v_usedLetOnly_1745_, uint8_t v_skipConstInApp_1746_, uint8_t v_skipInstances_1747_, lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc(v_a_1749_);
v___x_1756_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1756_, 0, lean_box(0));
lean_closure_set(v___x_1756_, 1, lean_box(0));
lean_closure_set(v___x_1756_, 2, v_a_1749_);
v___x_1757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___x_1756_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1811_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1811_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1811_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1810_; 
v_fst_1762_ = lean_ctor_get(v_a_1758_, 0);
v_snd_1763_ = lean_ctor_get(v_a_1758_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1758_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1765_ = v_a_1758_;
v_isShared_1766_ = v_isSharedCheck_1810_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_inc(v_fst_1762_);
lean_dec(v_a_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1810_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_fst_1762_, v_e_1748_);
lean_dec(v_fst_1762_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; 
lean_del_object(v___x_1765_);
lean_del_object(v___x_1760_);
v___x_1768_ = lean_box(v_usedLetOnly_1745_);
v___x_1769_ = lean_box(v_skipConstInApp_1746_);
v___x_1770_ = lean_box(v_skipInstances_1747_);
lean_inc_ref(v_e_1748_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1771_, 0, v_pre_1743_);
lean_closure_set(v___f_1771_, 1, v_e_1748_);
lean_closure_set(v___f_1771_, 2, v_post_1744_);
lean_closure_set(v___f_1771_, 3, v___x_1768_);
lean_closure_set(v___f_1771_, 4, v___x_1769_);
lean_closure_set(v___f_1771_, 5, v___x_1770_);
lean_inc_ref(v___y_1753_);
v___x_1772_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___f_1771_, v_a_1749_, v_snd_1763_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v_fst_1774_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_fst_1774_);
v_snd_1775_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_snd_1775_);
lean_dec(v_a_1773_);
lean_inc(v_fst_1774_);
lean_inc(v_a_1749_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1776_, 0, v_a_1749_);
lean_closure_set(v___f_1776_, 1, v_e_1748_);
lean_closure_set(v___f_1776_, 2, v_fst_1774_);
v___x_1777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(lean_box(0), v___f_1776_, v_snd_1775_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1794_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1794_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1794_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1792_; 
v_snd_1782_ = lean_ctor_get(v_a_1778_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_a_1778_, 0);
lean_dec(v_unused_1793_);
v___x_1784_ = v_a_1778_;
v_isShared_1785_ = v_isSharedCheck_1792_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_dec(v_a_1778_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1792_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v_fst_1774_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_fst_1774_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_snd_1782_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1787_);
v___x_1789_ = v___x_1780_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
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
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_fst_1774_);
v_a_1795_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1777_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1777_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_dec_ref(v_e_1748_);
return v___x_1772_;
}
}
else
{
lean_object* v_val_1803_; lean_object* v___x_1805_; 
lean_dec_ref(v_e_1748_);
lean_dec_ref(v_post_1744_);
lean_dec_ref(v_pre_1743_);
v_val_1803_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_val_1803_);
lean_dec_ref(v___x_1767_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_val_1803_);
v___x_1805_ = v___x_1765_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_val_1803_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_snd_1763_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1805_);
v___x_1807_ = v___x_1760_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_e_1748_);
lean_dec_ref(v_post_1744_);
lean_dec_ref(v_pre_1743_);
v_a_1812_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1757_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1757_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(lean_object* v_fvars_1820_, lean_object* v_pre_1821_, lean_object* v_post_1822_, lean_object* v_usedLetOnly_1823_, lean_object* v_skipConstInApp_1824_, lean_object* v_skipInstances_1825_, lean_object* v_body_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
uint8_t v_usedLetOnly_boxed_1835_; uint8_t v_skipConstInApp_boxed_1836_; uint8_t v_skipInstances_boxed_1837_; lean_object* v_res_1838_; 
v_usedLetOnly_boxed_1835_ = lean_unbox(v_usedLetOnly_1823_);
v_skipConstInApp_boxed_1836_ = lean_unbox(v_skipConstInApp_1824_);
v_skipInstances_boxed_1837_ = lean_unbox(v_skipInstances_1825_);
v_res_1838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_1820_, v_pre_1821_, v_post_1822_, v_usedLetOnly_boxed_1835_, v_skipConstInApp_boxed_1836_, v_skipInstances_boxed_1837_, v_body_1826_, v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1828_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(lean_object* v_pre_1839_, lean_object* v_post_1840_, uint8_t v_usedLetOnly_1841_, uint8_t v_skipConstInApp_1842_, uint8_t v_skipInstances_1843_, lean_object* v_fvars_1844_, lean_object* v_e_1845_, lean_object* v_a_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
if (lean_obj_tag(v_e_1845_) == 7)
{
lean_object* v_binderName_1853_; lean_object* v_binderType_1854_; lean_object* v_body_1855_; uint8_t v_binderInfo_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_binderName_1853_ = lean_ctor_get(v_e_1845_, 0);
lean_inc(v_binderName_1853_);
v_binderType_1854_ = lean_ctor_get(v_e_1845_, 1);
lean_inc_ref(v_binderType_1854_);
v_body_1855_ = lean_ctor_get(v_e_1845_, 2);
lean_inc_ref(v_body_1855_);
v_binderInfo_1856_ = lean_ctor_get_uint8(v_e_1845_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1845_);
v___x_1857_ = lean_expr_instantiate_rev(v_binderType_1854_, v_fvars_1844_);
lean_dec_ref(v_binderType_1854_);
lean_inc_ref(v_post_1840_);
lean_inc_ref(v_pre_1839_);
v___x_1858_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1839_, v_post_1840_, v_usedLetOnly_1841_, v_skipConstInApp_1842_, v_skipInstances_1843_, v___x_1857_, v_a_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v_fst_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_fst_1860_);
v_snd_1861_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_a_1859_);
v___x_1862_ = lean_box(v_usedLetOnly_1841_);
v___x_1863_ = lean_box(v_skipConstInApp_1842_);
v___x_1864_ = lean_box(v_skipInstances_1843_);
v___f_1865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed), 15, 7);
lean_closure_set(v___f_1865_, 0, v_fvars_1844_);
lean_closure_set(v___f_1865_, 1, v_pre_1839_);
lean_closure_set(v___f_1865_, 2, v_post_1840_);
lean_closure_set(v___f_1865_, 3, v___x_1862_);
lean_closure_set(v___f_1865_, 4, v___x_1863_);
lean_closure_set(v___f_1865_, 5, v___x_1864_);
lean_closure_set(v___f_1865_, 6, v_body_1855_);
v___x_1866_ = 0;
v___x_1867_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_binderName_1853_, v_binderInfo_1856_, v_fst_1860_, v___f_1865_, v___x_1866_, v_a_1846_, v_snd_1861_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1867_;
}
else
{
lean_dec_ref(v_body_1855_);
lean_dec(v_binderName_1853_);
lean_dec_ref(v_fvars_1844_);
lean_dec_ref(v_post_1840_);
lean_dec_ref(v_pre_1839_);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_expr_instantiate_rev(v_e_1845_, v_fvars_1844_);
lean_dec_ref(v_e_1845_);
lean_inc_ref(v_post_1840_);
lean_inc_ref(v_pre_1839_);
v___x_1869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1839_, v_post_1840_, v_usedLetOnly_1841_, v_skipConstInApp_1842_, v_skipInstances_1843_, v___x_1868_, v_a_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_fst_1871_; lean_object* v_snd_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
v_fst_1871_ = lean_ctor_get(v_a_1870_, 0);
lean_inc(v_fst_1871_);
v_snd_1872_ = lean_ctor_get(v_a_1870_, 1);
lean_inc(v_snd_1872_);
lean_dec(v_a_1870_);
v___x_1873_ = 0;
v___x_1874_ = 1;
v___x_1875_ = 1;
v___x_1876_ = l_Lean_Meta_mkForallFVars(v_fvars_1844_, v_fst_1871_, v___x_1873_, v_usedLetOnly_1841_, v___x_1874_, v___x_1875_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v_fvars_1844_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1839_, v_post_1840_, v_usedLetOnly_1841_, v_skipConstInApp_1842_, v_skipInstances_1843_, v_a_1877_, v_a_1846_, v_snd_1872_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1878_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_snd_1872_);
lean_dec_ref(v_post_1840_);
lean_dec_ref(v_pre_1839_);
v_a_1879_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1876_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1876_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_dec_ref(v_fvars_1844_);
lean_dec_ref(v_post_1840_);
lean_dec_ref(v_pre_1839_);
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(lean_object* v_fvars_1887_, lean_object* v_pre_1888_, lean_object* v_post_1889_, uint8_t v_usedLetOnly_1890_, uint8_t v_skipConstInApp_1891_, uint8_t v_skipInstances_1892_, lean_object* v_body_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_array_push(v_fvars_1887_, v_x_1894_);
v___x_1903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1888_, v_post_1889_, v_usedLetOnly_1890_, v_skipConstInApp_1891_, v_skipInstances_1892_, v___x_1902_, v_body_1893_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(lean_object* v_pre_1904_, lean_object* v_post_1905_, lean_object* v_usedLetOnly_1906_, lean_object* v_skipConstInApp_1907_, lean_object* v_skipInstances_1908_, lean_object* v_sz_1909_, lean_object* v_i_1910_, lean_object* v_bs_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
uint8_t v_usedLetOnly_boxed_1919_; uint8_t v_skipConstInApp_boxed_1920_; uint8_t v_skipInstances_boxed_1921_; size_t v_sz_boxed_1922_; size_t v_i_boxed_1923_; lean_object* v_res_1924_; 
v_usedLetOnly_boxed_1919_ = lean_unbox(v_usedLetOnly_1906_);
v_skipConstInApp_boxed_1920_ = lean_unbox(v_skipConstInApp_1907_);
v_skipInstances_boxed_1921_ = lean_unbox(v_skipInstances_1908_);
v_sz_boxed_1922_ = lean_unbox_usize(v_sz_1909_);
lean_dec(v_sz_1909_);
v_i_boxed_1923_ = lean_unbox_usize(v_i_1910_);
lean_dec(v_i_1910_);
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_1904_, v_post_1905_, v_usedLetOnly_boxed_1919_, v_skipConstInApp_boxed_1920_, v_skipInstances_boxed_1921_, v_sz_boxed_1922_, v_i_boxed_1923_, v_bs_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1912_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(lean_object* v_pre_1925_, lean_object* v_post_1926_, lean_object* v_usedLetOnly_1927_, lean_object* v_skipConstInApp_1928_, lean_object* v_skipInstances_1929_, lean_object* v_e_1930_, lean_object* v_a_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
uint8_t v_usedLetOnly_boxed_1938_; uint8_t v_skipConstInApp_boxed_1939_; uint8_t v_skipInstances_boxed_1940_; lean_object* v_res_1941_; 
v_usedLetOnly_boxed_1938_ = lean_unbox(v_usedLetOnly_1927_);
v_skipConstInApp_boxed_1939_ = lean_unbox(v_skipConstInApp_1928_);
v_skipInstances_boxed_1940_ = lean_unbox(v_skipInstances_1929_);
v_res_1941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_pre_1925_, v_post_1926_, v_usedLetOnly_boxed_1938_, v_skipConstInApp_boxed_1939_, v_skipInstances_boxed_1940_, v_e_1930_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v_a_1931_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(lean_object* v_pre_1942_, lean_object* v_post_1943_, lean_object* v_usedLetOnly_1944_, lean_object* v_skipConstInApp_1945_, lean_object* v_skipInstances_1946_, lean_object* v_fvars_1947_, lean_object* v_e_1948_, lean_object* v_a_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
uint8_t v_usedLetOnly_boxed_1956_; uint8_t v_skipConstInApp_boxed_1957_; uint8_t v_skipInstances_boxed_1958_; lean_object* v_res_1959_; 
v_usedLetOnly_boxed_1956_ = lean_unbox(v_usedLetOnly_1944_);
v_skipConstInApp_boxed_1957_ = lean_unbox(v_skipConstInApp_1945_);
v_skipInstances_boxed_1958_ = lean_unbox(v_skipInstances_1946_);
v_res_1959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_1942_, v_post_1943_, v_usedLetOnly_boxed_1956_, v_skipConstInApp_boxed_1957_, v_skipInstances_boxed_1958_, v_fvars_1947_, v_e_1948_, v_a_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_a_1949_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(lean_object* v_pre_1960_, lean_object* v_post_1961_, lean_object* v_usedLetOnly_1962_, lean_object* v_skipConstInApp_1963_, lean_object* v_skipInstances_1964_, lean_object* v_fvars_1965_, lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v_usedLetOnly_boxed_1974_; uint8_t v_skipConstInApp_boxed_1975_; uint8_t v_skipInstances_boxed_1976_; lean_object* v_res_1977_; 
v_usedLetOnly_boxed_1974_ = lean_unbox(v_usedLetOnly_1962_);
v_skipConstInApp_boxed_1975_ = lean_unbox(v_skipConstInApp_1963_);
v_skipInstances_boxed_1976_ = lean_unbox(v_skipInstances_1964_);
v_res_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_1960_, v_post_1961_, v_usedLetOnly_boxed_1974_, v_skipConstInApp_boxed_1975_, v_skipInstances_boxed_1976_, v_fvars_1965_, v_e_1966_, v_a_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_a_1967_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(lean_object* v_pre_1978_, lean_object* v_post_1979_, lean_object* v_usedLetOnly_1980_, lean_object* v_skipConstInApp_1981_, lean_object* v_skipInstances_1982_, lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_usedLetOnly_boxed_1991_; uint8_t v_skipConstInApp_boxed_1992_; uint8_t v_skipInstances_boxed_1993_; lean_object* v_res_1994_; 
v_usedLetOnly_boxed_1991_ = lean_unbox(v_usedLetOnly_1980_);
v_skipConstInApp_boxed_1992_ = lean_unbox(v_skipConstInApp_1981_);
v_skipInstances_boxed_1993_ = lean_unbox(v_skipInstances_1982_);
v_res_1994_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_1978_, v_post_1979_, v_usedLetOnly_boxed_1991_, v_skipConstInApp_boxed_1992_, v_skipInstances_boxed_1993_, v_e_1983_, v_a_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v_a_1984_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(lean_object* v_pre_1995_, lean_object* v_post_1996_, lean_object* v_usedLetOnly_1997_, lean_object* v_skipConstInApp_1998_, lean_object* v_skipInstances_1999_, lean_object* v_fvars_2000_, lean_object* v_e_2001_, lean_object* v_a_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v_usedLetOnly_boxed_2009_; uint8_t v_skipConstInApp_boxed_2010_; uint8_t v_skipInstances_boxed_2011_; lean_object* v_res_2012_; 
v_usedLetOnly_boxed_2009_ = lean_unbox(v_usedLetOnly_1997_);
v_skipConstInApp_boxed_2010_ = lean_unbox(v_skipConstInApp_1998_);
v_skipInstances_boxed_2011_ = lean_unbox(v_skipInstances_1999_);
v_res_2012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_pre_1995_, v_post_1996_, v_usedLetOnly_boxed_2009_, v_skipConstInApp_boxed_2010_, v_skipInstances_boxed_2011_, v_fvars_2000_, v_e_2001_, v_a_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v_a_2002_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_2013_, lean_object* v___x_2014_, lean_object* v_pre_2015_, lean_object* v_post_2016_, lean_object* v_usedLetOnly_2017_, lean_object* v_skipConstInApp_2018_, lean_object* v_skipInstances_2019_, lean_object* v_a_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_usedLetOnly_boxed_2029_; uint8_t v_skipConstInApp_boxed_2030_; uint8_t v_skipInstances_boxed_2031_; lean_object* v_res_2032_; 
v_usedLetOnly_boxed_2029_ = lean_unbox(v_usedLetOnly_2017_);
v_skipConstInApp_boxed_2030_ = lean_unbox(v_skipConstInApp_2018_);
v_skipInstances_boxed_2031_ = lean_unbox(v_skipInstances_2019_);
v_res_2032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2013_, v___x_2014_, v_pre_2015_, v_post_2016_, v_usedLetOnly_boxed_2029_, v_skipConstInApp_boxed_2030_, v_skipInstances_boxed_2031_, v_a_2020_, v_b_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2022_);
lean_dec_ref(v___x_2014_);
lean_dec(v_upperBound_2013_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(lean_object* v_skipInstances_2033_, lean_object* v_pre_2034_, lean_object* v_post_2035_, lean_object* v_usedLetOnly_2036_, lean_object* v_skipConstInApp_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_skipInstances_boxed_2048_; uint8_t v_usedLetOnly_boxed_2049_; uint8_t v_skipConstInApp_boxed_2050_; lean_object* v_res_2051_; 
v_skipInstances_boxed_2048_ = lean_unbox(v_skipInstances_2033_);
v_usedLetOnly_boxed_2049_ = lean_unbox(v_usedLetOnly_2036_);
v_skipConstInApp_boxed_2050_ = lean_unbox(v_skipConstInApp_2037_);
v_res_2051_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_skipInstances_boxed_2048_, v_pre_2034_, v_post_2035_, v_usedLetOnly_boxed_2049_, v_skipConstInApp_boxed_2050_, v_x_2038_, v_x_2039_, v_x_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2041_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_object* v_00_u03b1_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_apply_1(v_x_2053_, lean_box(0));
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___y_2054_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(v_00_u03b1_2063_, v_x_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2071_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_unsigned_to_nat(16u);
v___x_2074_ = lean_mk_array(v___x_2073_, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1);
v___x_2079_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2079_, 0, lean_box(0));
lean_closure_set(v___x_2079_, 1, lean_box(0));
lean_closure_set(v___x_2079_, 2, v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(lean_object* v_input_2080_, lean_object* v_pre_2081_, lean_object* v_post_2082_, uint8_t v_usedLetOnly_2083_, uint8_t v_skipConstInApp_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_a_2093_; lean_object* v_fst_2094_; lean_object* v_snd_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2);
v___x_2092_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2091_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
v_fst_2094_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_fst_2094_);
v_snd_2095_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_snd_2095_);
lean_dec(v_a_2093_);
v___x_2096_ = 0;
v___x_2097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_2081_, v_post_2082_, v_usedLetOnly_2083_, v_skipConstInApp_2084_, v___x_2096_, v_input_2080_, v_fst_2094_, v_snd_2095_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v_fst_2099_; lean_object* v_snd_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2119_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v_fst_2099_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_fst_2099_);
v_snd_2100_ = lean_ctor_get(v_a_2098_, 1);
lean_inc(v_snd_2100_);
lean_dec(v_a_2098_);
v___x_2101_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2101_, 0, lean_box(0));
lean_closure_set(v___x_2101_, 1, lean_box(0));
lean_closure_set(v___x_2101_, 2, v_fst_2094_);
v___x_2102_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(lean_box(0), v___x_2101_, v_snd_2100_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2119_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2119_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_snd_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_snd_2107_ = lean_ctor_get(v_a_2103_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2103_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_a_2103_, 0);
lean_dec(v_unused_2118_);
v___x_2109_ = v_a_2103_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snd_2107_);
lean_dec(v_a_2103_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v_fst_2099_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_fst_2099_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_snd_2107_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2112_);
v___x_2114_ = v___x_2105_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
else
{
lean_dec(v_fst_2094_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(lean_object* v_input_2120_, lean_object* v_pre_2121_, lean_object* v_post_2122_, lean_object* v_usedLetOnly_2123_, lean_object* v_skipConstInApp_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v_usedLetOnly_boxed_2131_; uint8_t v_skipConstInApp_boxed_2132_; lean_object* v_res_2133_; 
v_usedLetOnly_boxed_2131_ = lean_unbox(v_usedLetOnly_2123_);
v_skipConstInApp_boxed_2132_ = lean_unbox(v_skipConstInApp_2124_);
v_res_2133_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_input_2120_, v_pre_2121_, v_post_2122_, v_usedLetOnly_boxed_2131_, v_skipConstInApp_boxed_2132_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2133_;
}
}
static uint64_t _init_l_Lean_Meta_expandCoe___closed__2(void){
_start:
{
uint8_t v___x_2136_; uint64_t v___x_2137_; 
v___x_2136_ = 3;
v___x_2137_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe(lean_object* v_e_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2144_; uint8_t v_foApprox_2145_; uint8_t v_ctxApprox_2146_; uint8_t v_quasiPatternApprox_2147_; uint8_t v_constApprox_2148_; uint8_t v_isDefEqStuckEx_2149_; uint8_t v_unificationHints_2150_; uint8_t v_proofIrrelevance_2151_; uint8_t v_assignSyntheticOpaque_2152_; uint8_t v_offsetCnstrs_2153_; uint8_t v_etaStruct_2154_; uint8_t v_univApprox_2155_; uint8_t v_iota_2156_; uint8_t v_beta_2157_; uint8_t v_proj_2158_; uint8_t v_zeta_2159_; uint8_t v_zetaDelta_2160_; uint8_t v_zetaUnused_2161_; uint8_t v_zetaHave_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2193_; 
v___x_2144_ = l_Lean_Meta_Context_config(v_a_2139_);
v_foApprox_2145_ = lean_ctor_get_uint8(v___x_2144_, 0);
v_ctxApprox_2146_ = lean_ctor_get_uint8(v___x_2144_, 1);
v_quasiPatternApprox_2147_ = lean_ctor_get_uint8(v___x_2144_, 2);
v_constApprox_2148_ = lean_ctor_get_uint8(v___x_2144_, 3);
v_isDefEqStuckEx_2149_ = lean_ctor_get_uint8(v___x_2144_, 4);
v_unificationHints_2150_ = lean_ctor_get_uint8(v___x_2144_, 5);
v_proofIrrelevance_2151_ = lean_ctor_get_uint8(v___x_2144_, 6);
v_assignSyntheticOpaque_2152_ = lean_ctor_get_uint8(v___x_2144_, 7);
v_offsetCnstrs_2153_ = lean_ctor_get_uint8(v___x_2144_, 8);
v_etaStruct_2154_ = lean_ctor_get_uint8(v___x_2144_, 10);
v_univApprox_2155_ = lean_ctor_get_uint8(v___x_2144_, 11);
v_iota_2156_ = lean_ctor_get_uint8(v___x_2144_, 12);
v_beta_2157_ = lean_ctor_get_uint8(v___x_2144_, 13);
v_proj_2158_ = lean_ctor_get_uint8(v___x_2144_, 14);
v_zeta_2159_ = lean_ctor_get_uint8(v___x_2144_, 15);
v_zetaDelta_2160_ = lean_ctor_get_uint8(v___x_2144_, 16);
v_zetaUnused_2161_ = lean_ctor_get_uint8(v___x_2144_, 17);
v_zetaHave_2162_ = lean_ctor_get_uint8(v___x_2144_, 18);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2164_ = v___x_2144_;
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2144_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2193_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v_trackZetaDelta_2166_; lean_object* v_zetaDeltaSet_2167_; lean_object* v_lctx_2168_; lean_object* v_localInstances_2169_; lean_object* v_defEqCtx_x3f_2170_; lean_object* v_synthPendingDepth_2171_; lean_object* v_canUnfold_x3f_2172_; uint8_t v_univApprox_2173_; uint8_t v_inTypeClassResolution_2174_; uint8_t v_cacheInferType_2175_; uint8_t v___x_2176_; lean_object* v_config_2178_; 
v_trackZetaDelta_2166_ = lean_ctor_get_uint8(v_a_2139_, sizeof(void*)*7);
v_zetaDeltaSet_2167_ = lean_ctor_get(v_a_2139_, 1);
v_lctx_2168_ = lean_ctor_get(v_a_2139_, 2);
v_localInstances_2169_ = lean_ctor_get(v_a_2139_, 3);
v_defEqCtx_x3f_2170_ = lean_ctor_get(v_a_2139_, 4);
v_synthPendingDepth_2171_ = lean_ctor_get(v_a_2139_, 5);
v_canUnfold_x3f_2172_ = lean_ctor_get(v_a_2139_, 6);
v_univApprox_2173_ = lean_ctor_get_uint8(v_a_2139_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2174_ = lean_ctor_get_uint8(v_a_2139_, sizeof(void*)*7 + 2);
v_cacheInferType_2175_ = lean_ctor_get_uint8(v_a_2139_, sizeof(void*)*7 + 3);
v___x_2176_ = 3;
if (v_isShared_2165_ == 0)
{
v_config_2178_ = v___x_2164_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 0, v_foApprox_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 1, v_ctxApprox_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 2, v_quasiPatternApprox_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 3, v_constApprox_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 4, v_isDefEqStuckEx_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 5, v_unificationHints_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 6, v_proofIrrelevance_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 7, v_assignSyntheticOpaque_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 8, v_offsetCnstrs_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 10, v_etaStruct_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 11, v_univApprox_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 12, v_iota_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 13, v_beta_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 14, v_proj_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 15, v_zeta_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 16, v_zetaDelta_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 17, v_zetaUnused_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, 18, v_zetaHave_2162_);
v_config_2178_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
uint64_t v___x_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; uint64_t v___x_2186_; uint64_t v___x_2187_; uint64_t v_key_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_ctor_set_uint8(v_config_2178_, 9, v___x_2176_);
v___x_2179_ = l_Lean_Meta_Context_configKey(v_a_2139_);
v___x_2180_ = 2ULL;
v___x_2181_ = lean_uint64_shift_right(v___x_2179_, v___x_2180_);
v___f_2182_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__0));
v___f_2183_ = ((lean_object*)(l_Lean_Meta_expandCoe___closed__1));
v___x_2184_ = 0;
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_uint64_shift_left(v___x_2181_, v___x_2180_);
v___x_2187_ = lean_uint64_once(&l_Lean_Meta_expandCoe___closed__2, &l_Lean_Meta_expandCoe___closed__2_once, _init_l_Lean_Meta_expandCoe___closed__2);
v_key_2188_ = lean_uint64_lor(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2189_, 0, v_config_2178_);
lean_ctor_set_uint64(v___x_2189_, sizeof(void*)*1, v_key_2188_);
lean_inc(v_canUnfold_x3f_2172_);
lean_inc(v_synthPendingDepth_2171_);
lean_inc(v_defEqCtx_x3f_2170_);
lean_inc_ref(v_localInstances_2169_);
lean_inc_ref(v_lctx_2168_);
lean_inc(v_zetaDeltaSet_2167_);
v___x_2190_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_zetaDeltaSet_2167_);
lean_ctor_set(v___x_2190_, 2, v_lctx_2168_);
lean_ctor_set(v___x_2190_, 3, v_localInstances_2169_);
lean_ctor_set(v___x_2190_, 4, v_defEqCtx_x3f_2170_);
lean_ctor_set(v___x_2190_, 5, v_synthPendingDepth_2171_);
lean_ctor_set(v___x_2190_, 6, v_canUnfold_x3f_2172_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*7, v_trackZetaDelta_2166_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*7 + 1, v_univApprox_2173_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2174_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*7 + 3, v_cacheInferType_2175_);
v___x_2191_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(v_e_2138_, v___f_2183_, v___f_2182_, v___x_2184_, v___x_2184_, v___x_2185_, v___x_2190_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec_ref(v___x_2190_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_expandCoe___boxed(lean_object* v_e_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_expandCoe(v_e_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(lean_object* v_cls_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___redArg(v_cls_2201_, v___y_2202_, v___y_2205_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(lean_object* v_00_u03b2_2217_, lean_object* v_m_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_2218_, v_a_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_m_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_2221_, v_m_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_m_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
uint8_t v_res_2232_; lean_object* v_r_2233_; 
v_res_2232_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_2229_, v_x_2230_, v_x_2231_);
lean_dec_ref(v_x_2231_);
v_r_2233_ = lean_box(v_res_2232_);
return v_r_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2234_, lean_object* v_a_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___redArg(v_a_2235_, v_x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2238_, lean_object* v_a_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__6(v_00_u03b2_2238_, v_a_2239_, v_x_2240_);
lean_dec(v_x_2240_);
lean_dec(v_a_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(lean_object* v_upperBound_2242_, lean_object* v___x_2243_, lean_object* v_pre_2244_, lean_object* v_post_2245_, uint8_t v_usedLetOnly_2246_, uint8_t v_skipConstInApp_2247_, uint8_t v_skipInstances_2248_, lean_object* v___x_2249_, lean_object* v_inst_2250_, lean_object* v_R_2251_, lean_object* v_a_2252_, lean_object* v_b_2253_, lean_object* v_c_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_upperBound_2242_, v___x_2243_, v_pre_2244_, v_post_2245_, v_usedLetOnly_2246_, v_skipConstInApp_2247_, v_skipInstances_2248_, v_a_2252_, v_b_2253_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_2263_ = _args[0];
lean_object* v___x_2264_ = _args[1];
lean_object* v_pre_2265_ = _args[2];
lean_object* v_post_2266_ = _args[3];
lean_object* v_usedLetOnly_2267_ = _args[4];
lean_object* v_skipConstInApp_2268_ = _args[5];
lean_object* v_skipInstances_2269_ = _args[6];
lean_object* v___x_2270_ = _args[7];
lean_object* v_inst_2271_ = _args[8];
lean_object* v_R_2272_ = _args[9];
lean_object* v_a_2273_ = _args[10];
lean_object* v_b_2274_ = _args[11];
lean_object* v_c_2275_ = _args[12];
lean_object* v___y_2276_ = _args[13];
lean_object* v___y_2277_ = _args[14];
lean_object* v___y_2278_ = _args[15];
lean_object* v___y_2279_ = _args[16];
lean_object* v___y_2280_ = _args[17];
lean_object* v___y_2281_ = _args[18];
lean_object* v___y_2282_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2283_; uint8_t v_skipConstInApp_boxed_2284_; uint8_t v_skipInstances_boxed_2285_; lean_object* v_res_2286_; 
v_usedLetOnly_boxed_2283_ = lean_unbox(v_usedLetOnly_2267_);
v_skipConstInApp_boxed_2284_ = lean_unbox(v_skipConstInApp_2268_);
v_skipInstances_boxed_2285_ = lean_unbox(v_skipInstances_2269_);
v_res_2286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_upperBound_2263_, v___x_2264_, v_pre_2265_, v_post_2266_, v_usedLetOnly_boxed_2283_, v_skipConstInApp_boxed_2284_, v_skipInstances_boxed_2285_, v___x_2270_, v_inst_2271_, v_R_2272_, v_a_2273_, v_b_2274_, v_c_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2276_);
lean_dec(v___x_2270_);
lean_dec_ref(v___x_2264_);
lean_dec(v_upperBound_2263_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(lean_object* v_00_u03b2_2287_, lean_object* v_m_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___redArg(v_m_2288_, v_a_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(lean_object* v_00_u03b2_2291_, lean_object* v_m_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_00_u03b2_2291_, v_m_2292_, v_a_2293_);
lean_dec_ref(v_a_2293_);
lean_dec_ref(v_m_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17(lean_object* v_00_u03b1_2295_, lean_object* v_name_2296_, uint8_t v_bi_2297_, lean_object* v_type_2298_, lean_object* v_k_2299_, uint8_t v_kind_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___redArg(v_name_2296_, v_bi_2297_, v_type_2298_, v_k_2299_, v_kind_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_name_2310_, lean_object* v_bi_2311_, lean_object* v_type_2312_, lean_object* v_k_2313_, lean_object* v_kind_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_bi_boxed_2322_; uint8_t v_kind_boxed_2323_; lean_object* v_res_2324_; 
v_bi_boxed_2322_ = lean_unbox(v_bi_2311_);
v_kind_boxed_2323_ = lean_unbox(v_kind_2314_);
v_res_2324_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13_spec__17(v_00_u03b1_2309_, v_name_2310_, v_bi_boxed_2322_, v_type_2312_, v_k_2313_, v_kind_boxed_2323_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2315_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20(lean_object* v_00_u03b1_2325_, lean_object* v_name_2326_, lean_object* v_type_2327_, lean_object* v_val_2328_, lean_object* v_k_2329_, uint8_t v_nondep_2330_, uint8_t v_kind_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___redArg(v_name_2326_, v_type_2327_, v_val_2328_, v_k_2329_, v_nondep_2330_, v_kind_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_name_2341_, lean_object* v_type_2342_, lean_object* v_val_2343_, lean_object* v_k_2344_, lean_object* v_nondep_2345_, lean_object* v_kind_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_nondep_boxed_2354_; uint8_t v_kind_boxed_2355_; lean_object* v_res_2356_; 
v_nondep_boxed_2354_ = lean_unbox(v_nondep_2345_);
v_kind_boxed_2355_ = lean_unbox(v_kind_2346_);
v_res_2356_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15_spec__20(v_00_u03b1_2340_, v_name_2341_, v_type_2342_, v_val_2343_, v_k_2344_, v_nondep_boxed_2354_, v_kind_boxed_2355_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2347_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23(lean_object* v_00_u03b1_2357_, lean_object* v_ref_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___redArg(v_ref_2358_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_ref_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__23(v_00_u03b1_2365_, v_ref_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(lean_object* v_00_u03b1_2373_, lean_object* v_x_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
lean_inc_ref(v___y_2379_);
v___x_2382_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_x_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(v_00_u03b1_2383_, v_x_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2385_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18(lean_object* v_00_u03b2_2393_, lean_object* v_m_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18___redArg(v_m_2394_, v_a_2395_, v_b_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2398_, lean_object* v_x_2399_, size_t v_x_2400_, lean_object* v_x_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2399_, v_x_2400_, v_x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
size_t v_x_39050__boxed_2407_; uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_x_39050__boxed_2407_ = lean_unbox_usize(v_x_2405_);
lean_dec(v_x_2405_);
v_res_2408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2403_, v_x_2404_, v_x_39050__boxed_2407_, v_x_2406_);
lean_dec_ref(v_x_2406_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15(lean_object* v_00_u03b2_2410_, lean_object* v_a_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___redArg(v_a_2411_, v_x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2414_, lean_object* v_a_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__15(v_00_u03b2_2414_, v_a_2415_, v_x_2416_);
lean_dec(v_x_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25(lean_object* v_00_u03b2_2418_, lean_object* v_a_2419_, lean_object* v_x_2420_){
_start:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___redArg(v_a_2419_, v_x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25___boxed(lean_object* v_00_u03b2_2422_, lean_object* v_a_2423_, lean_object* v_x_2424_){
_start:
{
uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_res_2425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__25(v_00_u03b2_2422_, v_a_2423_, v_x_2424_);
lean_dec(v_x_2424_);
lean_dec_ref(v_a_2423_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26(lean_object* v_00_u03b2_2427_, lean_object* v_data_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26___redArg(v_data_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27(lean_object* v_00_u03b2_2430_, lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__27___redArg(v_a_2431_, v_b_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2435_, lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_heq_2438_, lean_object* v_i_2439_, lean_object* v_k_2440_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_2436_, v_i_2439_, v_k_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_heq_2445_, lean_object* v_i_2446_, lean_object* v_k_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_2442_, v_keys_2443_, v_vals_2444_, v_heq_2445_, v_i_2446_, v_k_2447_);
lean_dec_ref(v_k_2447_);
lean_dec_ref(v_vals_2444_);
lean_dec_ref(v_keys_2443_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28(lean_object* v_00_u03b2_2450_, lean_object* v_i_2451_, lean_object* v_source_2452_, lean_object* v_target_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28___redArg(v_i_2451_, v_source_2452_, v_target_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29(lean_object* v_00_u03b2_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__18_spec__26_spec__28_spec__29___redArg(v_x_2456_, v_x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(lean_object* v_name_2459_, lean_object* v_decl_2460_, lean_object* v_ref_2461_){
_start:
{
lean_object* v_defValue_2463_; lean_object* v_descr_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2491_; 
v_defValue_2463_ = lean_ctor_get(v_decl_2460_, 0);
v_descr_2464_ = lean_ctor_get(v_decl_2460_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_decl_2460_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2466_ = v_decl_2460_;
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_descr_2464_);
lean_inc(v_defValue_2463_);
lean_dec(v_decl_2460_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2468_ = lean_alloc_ctor(1, 0, 1);
v___x_2469_ = lean_unbox(v_defValue_2463_);
lean_ctor_set_uint8(v___x_2468_, 0, v___x_2469_);
lean_inc(v_name_2459_);
v___x_2470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2470_, 0, v_name_2459_);
lean_ctor_set(v___x_2470_, 1, v_ref_2461_);
lean_ctor_set(v___x_2470_, 2, v___x_2468_);
lean_ctor_set(v___x_2470_, 3, v_descr_2464_);
lean_inc(v_name_2459_);
v___x_2471_ = lean_register_option(v_name_2459_, v___x_2470_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2481_; 
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2471_, 0);
lean_dec(v_unused_2482_);
v___x_2473_ = v___x_2471_;
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v___x_2471_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v_defValue_2463_);
lean_ctor_set(v___x_2466_, 0, v_name_2459_);
v___x_2476_ = v___x_2466_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_name_2459_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_defValue_2463_);
v___x_2476_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2478_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2476_);
v___x_2478_ = v___x_2473_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_del_object(v___x_2466_);
lean_dec(v_defValue_2463_);
lean_dec(v_name_2459_);
v_a_2483_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2471_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2471_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2492_, lean_object* v_decl_2493_, lean_object* v_ref_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_2492_, v_decl_2493_, v_ref_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2511_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2512_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_));
v___x_2513_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_2510_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_ref_2522_; lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_ref_2522_ = lean_ctor_get(v___y_2519_, 5);
v___x_2523_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__3_spec__6(v_msg_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_inc(v_ref_2522_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_ref_2522_);
lean_ctor_set(v___x_2528_, 1, v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 1);
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2539_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f(lean_object* v_expr_2555_, lean_object* v_expectedType_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
lean_inc(v_a_2560_);
lean_inc_ref(v_a_2559_);
lean_inc(v_a_2558_);
lean_inc_ref(v_a_2557_);
lean_inc_ref(v_expr_2555_);
v___x_2562_ = lean_infer_type(v_expr_2555_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
lean_inc(v_a_2563_);
v___x_2564_ = l_Lean_Meta_getLevel(v_a_2563_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v___x_2564_);
lean_inc_ref(v_expectedType_2556_);
v___x_2566_ = l_Lean_Meta_getLevel(v_expectedType_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2565_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
lean_inc_ref(v___x_2571_);
v___x_2572_ = l_Lean_mkConst(v___x_2568_, v___x_2571_);
v___x_2573_ = lean_unsigned_to_nat(3u);
v___x_2574_ = lean_mk_empty_array_with_capacity(v___x_2573_);
lean_inc(v_a_2563_);
v___x_2575_ = lean_array_push(v___x_2574_, v_a_2563_);
lean_inc_ref(v_expr_2555_);
v___x_2576_ = lean_array_push(v___x_2575_, v_expr_2555_);
lean_inc_ref(v_expectedType_2556_);
v___x_2577_ = lean_array_push(v___x_2576_, v_expectedType_2556_);
v___x_2578_ = l_Lean_mkAppN(v___x_2572_, v___x_2577_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = lean_box(0);
v___x_2580_ = l_Lean_Meta_trySynthInstance(v___x_2578_, v___x_2579_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2678_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2678_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2678_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
switch(lean_obj_tag(v_a_2581_))
{
case 0:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec_ref(v___x_2571_);
lean_dec(v_a_2563_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v___x_2585_ = lean_box(0);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2585_);
v___x_2587_ = v___x_2583_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
case 1:
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2673_; 
lean_del_object(v___x_2583_);
v_a_2589_ = lean_ctor_get(v_a_2581_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_a_2581_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2591_ = v_a_2581_;
v_isShared_2592_ = v_isSharedCheck_2673_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v_a_2581_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2673_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2593_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2));
v___x_2594_ = l_Lean_mkConst(v___x_2593_, v___x_2571_);
v___x_2595_ = lean_unsigned_to_nat(4u);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2595_);
v___x_2597_ = lean_array_push(v___x_2596_, v_a_2563_);
lean_inc_ref(v_expr_2555_);
v___x_2598_ = lean_array_push(v___x_2597_, v_expr_2555_);
lean_inc_ref(v_expectedType_2556_);
v___x_2599_ = lean_array_push(v___x_2598_, v_expectedType_2556_);
v___x_2600_ = lean_array_push(v___x_2599_, v_a_2589_);
v___x_2601_ = l_Lean_mkAppN(v___x_2594_, v___x_2600_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = l_Lean_Meta_expandCoe(v___x_2601_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2664_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2664_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2664_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_fst_2614_; lean_object* v___x_2615_; 
v_fst_2614_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_a_2560_);
lean_inc_ref(v_a_2559_);
lean_inc(v_a_2558_);
lean_inc_ref(v_a_2557_);
lean_inc(v_fst_2614_);
v___x_2615_ = lean_infer_type(v_fst_2614_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2615_);
lean_inc_ref(v_expectedType_2556_);
v___x_2617_ = l_Lean_Meta_isExprDefEq(v_a_2616_, v_expectedType_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; uint8_t v___x_2619_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = lean_unbox(v_a_2618_);
lean_dec(v_a_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2645_; 
lean_inc(v_fst_2614_);
lean_del_object(v___x_2605_);
lean_del_object(v___x_2591_);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2603_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2646_ = lean_ctor_get(v_a_2603_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_a_2603_, 0);
lean_dec(v_unused_2647_);
v___x_2621_ = v_a_2603_;
v_isShared_2622_ = v_isSharedCheck_2645_;
goto v_resetjp_2620_;
}
else
{
lean_dec(v_a_2603_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2645_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4);
v___x_2624_ = l_Lean_indentExpr(v_expr_2555_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 7);
lean_ctor_set(v___x_2621_, 1, v___x_2624_);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v___x_2627_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Lean_indentExpr(v_expectedType_2556_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_obj_once(&l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8, &l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once, _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = l_Lean_indentExpr(v_fst_2614_);
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2634_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
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
else
{
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_del_object(v___x_2605_);
lean_dec(v_a_2603_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2648_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2617_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2617_);
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
lean_del_object(v___x_2605_);
lean_dec(v_a_2603_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2656_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2615_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2615_);
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
v___jp_2607_:
{
lean_object* v___x_2609_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_a_2603_);
v___x_2609_ = v___x_2591_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2603_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2609_);
v___x_2611_ = v___x_2605_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
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
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_del_object(v___x_2591_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2665_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2602_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2602_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
default: 
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec_ref(v___x_2571_);
lean_dec(v_a_2563_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v___x_2674_ = lean_box(2);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2674_);
v___x_2676_ = v___x_2583_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v___x_2571_);
lean_dec(v_a_2563_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2679_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2580_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2580_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_a_2565_);
lean_dec(v_a_2563_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2687_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2566_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2566_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
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
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2563_);
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2695_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2564_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2564_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
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
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_expectedType_2556_);
lean_dec_ref(v_expr_2555_);
v_a_2703_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2562_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2562_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(lean_object* v_expr_2711_, lean_object* v_expectedType_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2711_, v_expectedType_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(lean_object* v_00_u03b1_2719_, lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_msg_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(v_00_u03b1_2727_, v_msg_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f(lean_object* v_expr_2735_, lean_object* v_expectedType_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_2735_, v_expectedType_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2767_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
switch(lean_obj_tag(v_a_2743_))
{
case 0:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_box(0);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
case 1:
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2762_; 
v_a_2751_ = lean_ctor_get(v_a_2743_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2753_ = v_a_2743_;
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v_a_2743_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_fst_2755_; lean_object* v___x_2757_; 
v_fst_2755_ = lean_ctor_get(v_a_2751_, 0);
lean_inc(v_fst_2755_);
lean_dec(v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v_fst_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_fst_2755_);
v___x_2757_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2757_);
v___x_2759_ = v___x_2745_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
default: 
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = lean_box(2);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2763_);
v___x_2765_ = v___x_2745_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2742_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2742_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceSimple_x3f___boxed(lean_object* v_expr_2776_, lean_object* v_expectedType_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_coerceSimple_x3f(v_expr_2776_, v_expectedType_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__4(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__3));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__6(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__5));
v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToFunction_x3f___closed__8(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__7));
v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f(lean_object* v_expr_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2805_; 
lean_inc(v_a_2803_);
lean_inc_ref(v_a_2802_);
lean_inc(v_a_2801_);
lean_inc_ref(v_a_2800_);
lean_inc_ref(v_expr_2799_);
v___x_2805_ = lean_infer_type(v_expr_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
lean_inc(v_a_2806_);
v___x_2807_ = l_Lean_Meta_getLevel(v_a_2806_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___x_2809_);
lean_inc(v_a_2810_);
v___x_2811_ = l_Lean_mkSort(v_a_2810_);
lean_inc(v_a_2806_);
v___x_2812_ = l_Lean_mkArrow(v_a_2806_, v___x_2811_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_a_2813_);
v___x_2815_ = 0;
v___x_2816_ = lean_box(0);
v___x_2817_ = l_Lean_Meta_mkFreshExprMVar(v___x_2814_, v___x_2815_, v___x_2816_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__1));
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2810_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2808_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
lean_inc_ref(v___x_2822_);
v___x_2823_ = l_Lean_Expr_const___override(v___x_2819_, v___x_2822_);
lean_inc(v_a_2818_);
lean_inc(v_a_2806_);
v___x_2824_ = l_Lean_mkAppB(v___x_2823_, v_a_2806_, v_a_2818_);
v___x_2825_ = lean_box(0);
v___x_2826_ = l_Lean_Meta_trySynthInstance(v___x_2824_, v___x_2825_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2913_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2913_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2913_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
if (lean_obj_tag(v_a_2827_) == 1)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2909_; 
lean_del_object(v___x_2829_);
v_a_2831_ = lean_ctor_get(v_a_2827_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_a_2827_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2833_ = v_a_2827_;
v_isShared_2834_ = v_isSharedCheck_2909_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v_a_2827_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2909_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2835_ = ((lean_object*)(l_Lean_Meta_coerceToFunction_x3f___closed__2));
v___x_2836_ = l_Lean_Expr_const___override(v___x_2835_, v___x_2822_);
lean_inc_ref(v_expr_2799_);
lean_inc(v_a_2831_);
v___x_2837_ = l_Lean_mkApp4(v___x_2836_, v_a_2806_, v_a_2818_, v_a_2831_, v_expr_2799_);
v___x_2838_ = l_Lean_Meta_expandCoe(v___x_2837_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2900_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2900_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2900_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_fst_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2898_; 
v_fst_2843_ = lean_ctor_get(v_a_2839_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v_a_2839_, 1);
lean_dec(v_unused_2899_);
v___x_2845_ = v_a_2839_;
v_isShared_2846_ = v_isSharedCheck_2898_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_fst_2843_);
lean_dec(v_a_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2898_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2854_; 
lean_inc(v_a_2803_);
lean_inc_ref(v_a_2802_);
lean_inc(v_a_2801_);
lean_inc_ref(v_a_2800_);
lean_inc(v_fst_2843_);
v___x_2854_ = lean_infer_type(v_fst_2843_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2854_);
lean_inc(v_a_2803_);
lean_inc_ref(v_a_2802_);
lean_inc(v_a_2801_);
lean_inc_ref(v_a_2800_);
v___x_2856_ = lean_whnf(v_a_2855_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; uint8_t v___x_2858_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = l_Lean_Expr_isForall(v_a_2857_);
lean_dec(v_a_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
lean_del_object(v___x_2841_);
lean_del_object(v___x_2833_);
v___x_2859_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_2860_ = l_Lean_indentExpr(v_expr_2799_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 7);
lean_ctor_set(v___x_2845_, 1, v___x_2860_);
lean_ctor_set(v___x_2845_, 0, v___x_2859_);
v___x_2862_ = v___x_2845_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
v___x_2863_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__6, &l_Lean_Meta_coerceToFunction_x3f___closed__6_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__6);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_indentExpr(v_fst_2843_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__8, &l_Lean_Meta_coerceToFunction_x3f___closed__8_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__8);
v___x_2868_ = l_Lean_indentExpr(v_a_2831_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Lean_MessageData_hint_x27(v___x_2869_);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2866_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_2871_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_del_object(v___x_2845_);
lean_dec(v_a_2831_);
lean_dec_ref(v_expr_2799_);
goto v___jp_2847_;
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_del_object(v___x_2845_);
lean_dec(v_fst_2843_);
lean_del_object(v___x_2841_);
lean_del_object(v___x_2833_);
lean_dec(v_a_2831_);
lean_dec_ref(v_expr_2799_);
v_a_2882_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2856_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2856_);
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
lean_del_object(v___x_2845_);
lean_dec(v_fst_2843_);
lean_del_object(v___x_2841_);
lean_del_object(v___x_2833_);
lean_dec(v_a_2831_);
lean_dec_ref(v_expr_2799_);
v_a_2890_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2854_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2854_);
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
v___jp_2847_:
{
lean_object* v___x_2849_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v_fst_2843_);
v___x_2849_ = v___x_2833_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fst_2843_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2851_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2849_);
v___x_2851_ = v___x_2841_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2833_);
lean_dec(v_a_2831_);
lean_dec_ref(v_expr_2799_);
v_a_2901_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2838_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2838_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
else
{
lean_object* v___x_2911_; 
lean_dec(v_a_2827_);
lean_dec_ref(v___x_2822_);
lean_dec(v_a_2818_);
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2825_);
v___x_2911_ = v___x_2829_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2825_);
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
lean_dec_ref(v___x_2822_);
lean_dec(v_a_2818_);
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
v_a_2914_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2826_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2826_);
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
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2810_);
lean_dec(v_a_2808_);
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
v_a_2922_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2817_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2817_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2810_);
lean_dec(v_a_2808_);
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
v_a_2930_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2812_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2812_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2808_);
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
v_a_2938_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2809_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2809_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_a_2806_);
lean_dec_ref(v_expr_2799_);
v_a_2946_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2807_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2807_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_expr_2799_);
v_a_2954_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2805_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2805_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToFunction_x3f___boxed(lean_object* v_expr_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2968_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__4(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__3));
v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Meta_coerceToSort_x3f___closed__6(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__5));
v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f(lean_object* v_expr_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; 
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc(v_a_2983_);
lean_inc_ref(v_a_2982_);
lean_inc_ref(v_expr_2981_);
v___x_2987_ = lean_infer_type(v_expr_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref(v___x_2987_);
lean_inc(v_a_2988_);
v___x_2989_ = l_Lean_Meta_getLevel(v_a_2988_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
lean_inc(v_a_2992_);
v___x_2993_ = l_Lean_mkSort(v_a_2992_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = 0;
v___x_2996_ = lean_box(0);
v___x_2997_ = l_Lean_Meta_mkFreshExprMVar(v___x_2994_, v___x_2995_, v___x_2996_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__1));
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3001_, 0, v_a_2992_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_a_2990_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
lean_inc_ref(v___x_3002_);
v___x_3003_ = l_Lean_Expr_const___override(v___x_2999_, v___x_3002_);
lean_inc(v_a_2998_);
lean_inc(v_a_2988_);
v___x_3004_ = l_Lean_mkAppB(v___x_3003_, v_a_2988_, v_a_2998_);
v___x_3005_ = lean_box(0);
v___x_3006_ = l_Lean_Meta_trySynthInstance(v___x_3004_, v___x_3005_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3093_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3093_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3093_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
if (lean_obj_tag(v_a_3007_) == 1)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_3009_);
v_a_3011_ = lean_ctor_get(v_a_3007_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3013_ = v_a_3007_;
v_isShared_3014_ = v_isSharedCheck_3089_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v_a_3007_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3089_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3015_ = ((lean_object*)(l_Lean_Meta_coerceToSort_x3f___closed__2));
v___x_3016_ = l_Lean_Expr_const___override(v___x_3015_, v___x_3002_);
lean_inc_ref(v_expr_2981_);
lean_inc(v_a_3011_);
v___x_3017_ = l_Lean_mkApp4(v___x_3016_, v_a_2988_, v_a_2998_, v_a_3011_, v_expr_2981_);
v___x_3018_ = l_Lean_Meta_expandCoe(v___x_3017_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3080_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3080_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3080_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_fst_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3078_; 
v_fst_3023_ = lean_ctor_get(v_a_3019_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_a_3019_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v_a_3019_, 1);
lean_dec(v_unused_3079_);
v___x_3025_ = v_a_3019_;
v_isShared_3026_ = v_isSharedCheck_3078_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_fst_3023_);
lean_dec(v_a_3019_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3078_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3034_; 
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc(v_a_2983_);
lean_inc_ref(v_a_2982_);
lean_inc(v_fst_3023_);
v___x_3034_ = lean_infer_type(v_fst_3023_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc(v_a_2983_);
lean_inc_ref(v_a_2982_);
v___x_3036_ = lean_whnf(v_a_3035_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; uint8_t v___x_3038_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3036_);
v___x_3038_ = l_Lean_Expr_isSort(v_a_3037_);
lean_dec(v_a_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
lean_del_object(v___x_3021_);
lean_del_object(v___x_3013_);
v___x_3039_ = lean_obj_once(&l_Lean_Meta_coerceToFunction_x3f___closed__4, &l_Lean_Meta_coerceToFunction_x3f___closed__4_once, _init_l_Lean_Meta_coerceToFunction_x3f___closed__4);
v___x_3040_ = l_Lean_indentExpr(v_expr_2981_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 7);
lean_ctor_set(v___x_3025_, 1, v___x_3040_);
lean_ctor_set(v___x_3025_, 0, v___x_3039_);
v___x_3042_ = v___x_3025_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v___x_3043_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__4, &l_Lean_Meta_coerceToSort_x3f___closed__4_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__4);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_indentExpr(v_fst_3023_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Lean_Meta_coerceToSort_x3f___closed__6, &l_Lean_Meta_coerceToSort_x3f___closed__6_once, _init_l_Lean_Meta_coerceToSort_x3f___closed__6);
v___x_3048_ = l_Lean_indentExpr(v_a_3011_);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_MessageData_hint_x27(v___x_3049_);
v___x_3051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3046_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_3051_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_del_object(v___x_3025_);
lean_dec(v_a_3011_);
lean_dec_ref(v_expr_2981_);
goto v___jp_3027_;
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_del_object(v___x_3021_);
lean_del_object(v___x_3013_);
lean_dec(v_a_3011_);
lean_dec_ref(v_expr_2981_);
v_a_3062_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3036_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3036_);
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
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_del_object(v___x_3021_);
lean_del_object(v___x_3013_);
lean_dec(v_a_3011_);
lean_dec_ref(v_expr_2981_);
v_a_3070_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3034_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3034_);
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
v___jp_3027_:
{
lean_object* v___x_3029_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v_fst_3023_);
v___x_3029_ = v___x_3013_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_fst_3023_);
v___x_3029_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3029_);
v___x_3031_ = v___x_3021_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_del_object(v___x_3013_);
lean_dec(v_a_3011_);
lean_dec_ref(v_expr_2981_);
v_a_3081_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3018_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3018_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_a_3007_);
lean_dec_ref(v___x_3002_);
lean_dec(v_a_2998_);
lean_dec(v_a_2988_);
lean_dec_ref(v_expr_2981_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3005_);
v___x_3091_ = v___x_3009_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3005_);
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
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v___x_3002_);
lean_dec(v_a_2998_);
lean_dec(v_a_2988_);
lean_dec_ref(v_expr_2981_);
v_a_3094_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3006_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3006_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_2992_);
lean_dec(v_a_2990_);
lean_dec(v_a_2988_);
lean_dec_ref(v_expr_2981_);
v_a_3102_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_2997_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_2997_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_2990_);
lean_dec(v_a_2988_);
lean_dec_ref(v_expr_2981_);
v_a_3110_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_2991_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_2991_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_2988_);
lean_dec_ref(v_expr_2981_);
v_a_3118_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2989_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_2989_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_expr_2981_);
v_a_3126_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_2987_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_2987_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceToSort_x3f___boxed(lean_object* v_expr_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Meta_coerceToSort_x3f(v_expr_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(lean_object* v_e_3141_, lean_object* v___y_3142_){
_start:
{
uint8_t v___x_3144_; 
v___x_3144_ = l_Lean_Expr_hasMVar(v_e_3141_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_e_3141_);
return v___x_3145_;
}
else
{
lean_object* v___x_3146_; lean_object* v_mctx_3147_; lean_object* v___x_3148_; lean_object* v_fst_3149_; lean_object* v_snd_3150_; lean_object* v___x_3151_; lean_object* v_cache_3152_; lean_object* v_zetaDeltaFVarIds_3153_; lean_object* v_postponed_3154_; lean_object* v_diag_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3164_; 
v___x_3146_ = lean_st_ref_get(v___y_3142_);
v_mctx_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc_ref(v_mctx_3147_);
lean_dec(v___x_3146_);
v___x_3148_ = l_Lean_instantiateMVarsCore(v_mctx_3147_, v_e_3141_);
v_fst_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_fst_3149_);
v_snd_3150_ = lean_ctor_get(v___x_3148_, 1);
lean_inc(v_snd_3150_);
lean_dec_ref(v___x_3148_);
v___x_3151_ = lean_st_ref_take(v___y_3142_);
v_cache_3152_ = lean_ctor_get(v___x_3151_, 1);
v_zetaDeltaFVarIds_3153_ = lean_ctor_get(v___x_3151_, 2);
v_postponed_3154_ = lean_ctor_get(v___x_3151_, 3);
v_diag_3155_ = lean_ctor_get(v___x_3151_, 4);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v___x_3151_, 0);
lean_dec(v_unused_3165_);
v___x_3157_ = v___x_3151_;
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_diag_3155_);
lean_inc(v_postponed_3154_);
lean_inc(v_zetaDeltaFVarIds_3153_);
lean_inc(v_cache_3152_);
lean_dec(v___x_3151_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v_snd_3150_);
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_snd_3150_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_cache_3152_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_zetaDeltaFVarIds_3153_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v_postponed_3154_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v_diag_3155_);
v___x_3160_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_st_ref_set(v___y_3142_, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_fst_3149_);
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(lean_object* v_e_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3166_, v___y_3167_);
lean_dec(v___y_3167_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(lean_object* v_e_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_e_3170_, v___y_3172_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(lean_object* v_e_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(v_e_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3183_;
}
}
static uint64_t _init_l_Lean_Meta_isTypeApp_x3f___closed__0(void){
_start:
{
uint8_t v___x_3184_; uint64_t v___x_3185_; 
v___x_3184_ = 2;
v___x_3185_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f(lean_object* v_type_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; uint8_t v_foApprox_3193_; uint8_t v_ctxApprox_3194_; uint8_t v_quasiPatternApprox_3195_; uint8_t v_constApprox_3196_; uint8_t v_isDefEqStuckEx_3197_; uint8_t v_unificationHints_3198_; uint8_t v_proofIrrelevance_3199_; uint8_t v_assignSyntheticOpaque_3200_; uint8_t v_offsetCnstrs_3201_; uint8_t v_etaStruct_3202_; uint8_t v_univApprox_3203_; uint8_t v_iota_3204_; uint8_t v_beta_3205_; uint8_t v_proj_3206_; uint8_t v_zeta_3207_; uint8_t v_zetaDelta_3208_; uint8_t v_zetaUnused_3209_; uint8_t v_zetaHave_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3275_; 
v___x_3192_ = l_Lean_Meta_Context_config(v_a_3187_);
v_foApprox_3193_ = lean_ctor_get_uint8(v___x_3192_, 0);
v_ctxApprox_3194_ = lean_ctor_get_uint8(v___x_3192_, 1);
v_quasiPatternApprox_3195_ = lean_ctor_get_uint8(v___x_3192_, 2);
v_constApprox_3196_ = lean_ctor_get_uint8(v___x_3192_, 3);
v_isDefEqStuckEx_3197_ = lean_ctor_get_uint8(v___x_3192_, 4);
v_unificationHints_3198_ = lean_ctor_get_uint8(v___x_3192_, 5);
v_proofIrrelevance_3199_ = lean_ctor_get_uint8(v___x_3192_, 6);
v_assignSyntheticOpaque_3200_ = lean_ctor_get_uint8(v___x_3192_, 7);
v_offsetCnstrs_3201_ = lean_ctor_get_uint8(v___x_3192_, 8);
v_etaStruct_3202_ = lean_ctor_get_uint8(v___x_3192_, 10);
v_univApprox_3203_ = lean_ctor_get_uint8(v___x_3192_, 11);
v_iota_3204_ = lean_ctor_get_uint8(v___x_3192_, 12);
v_beta_3205_ = lean_ctor_get_uint8(v___x_3192_, 13);
v_proj_3206_ = lean_ctor_get_uint8(v___x_3192_, 14);
v_zeta_3207_ = lean_ctor_get_uint8(v___x_3192_, 15);
v_zetaDelta_3208_ = lean_ctor_get_uint8(v___x_3192_, 16);
v_zetaUnused_3209_ = lean_ctor_get_uint8(v___x_3192_, 17);
v_zetaHave_3210_ = lean_ctor_get_uint8(v___x_3192_, 18);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3212_ = v___x_3192_;
v_isShared_3213_ = v_isSharedCheck_3275_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v___x_3192_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3275_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
uint8_t v_trackZetaDelta_3214_; lean_object* v_zetaDeltaSet_3215_; lean_object* v_lctx_3216_; lean_object* v_localInstances_3217_; lean_object* v_defEqCtx_x3f_3218_; lean_object* v_synthPendingDepth_3219_; lean_object* v_canUnfold_x3f_3220_; uint8_t v_univApprox_3221_; uint8_t v_inTypeClassResolution_3222_; uint8_t v_cacheInferType_3223_; uint8_t v___x_3224_; lean_object* v_config_3226_; 
v_trackZetaDelta_3214_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*7);
v_zetaDeltaSet_3215_ = lean_ctor_get(v_a_3187_, 1);
v_lctx_3216_ = lean_ctor_get(v_a_3187_, 2);
v_localInstances_3217_ = lean_ctor_get(v_a_3187_, 3);
v_defEqCtx_x3f_3218_ = lean_ctor_get(v_a_3187_, 4);
v_synthPendingDepth_3219_ = lean_ctor_get(v_a_3187_, 5);
v_canUnfold_x3f_3220_ = lean_ctor_get(v_a_3187_, 6);
v_univApprox_3221_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3222_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*7 + 2);
v_cacheInferType_3223_ = lean_ctor_get_uint8(v_a_3187_, sizeof(void*)*7 + 3);
v___x_3224_ = 2;
if (v_isShared_3213_ == 0)
{
v_config_3226_ = v___x_3212_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 0, v_foApprox_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 1, v_ctxApprox_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 2, v_quasiPatternApprox_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 3, v_constApprox_3196_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 4, v_isDefEqStuckEx_3197_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 5, v_unificationHints_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 6, v_proofIrrelevance_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 7, v_assignSyntheticOpaque_3200_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 8, v_offsetCnstrs_3201_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 10, v_etaStruct_3202_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 11, v_univApprox_3203_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 12, v_iota_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 13, v_beta_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 14, v_proj_3206_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 15, v_zeta_3207_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 16, v_zetaDelta_3208_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 17, v_zetaUnused_3209_);
lean_ctor_set_uint8(v_reuseFailAlloc_3274_, 18, v_zetaHave_3210_);
v_config_3226_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
uint64_t v___x_3227_; uint64_t v___x_3228_; uint64_t v___x_3229_; uint64_t v___x_3230_; uint64_t v___x_3231_; uint64_t v_key_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_ctor_set_uint8(v_config_3226_, 9, v___x_3224_);
v___x_3227_ = l_Lean_Meta_Context_configKey(v_a_3187_);
v___x_3228_ = 2ULL;
v___x_3229_ = lean_uint64_shift_right(v___x_3227_, v___x_3228_);
v___x_3230_ = lean_uint64_shift_left(v___x_3229_, v___x_3228_);
v___x_3231_ = lean_uint64_once(&l_Lean_Meta_isTypeApp_x3f___closed__0, &l_Lean_Meta_isTypeApp_x3f___closed__0_once, _init_l_Lean_Meta_isTypeApp_x3f___closed__0);
v_key_3232_ = lean_uint64_lor(v___x_3230_, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3233_, 0, v_config_3226_);
lean_ctor_set_uint64(v___x_3233_, sizeof(void*)*1, v_key_3232_);
lean_inc(v_canUnfold_x3f_3220_);
lean_inc(v_synthPendingDepth_3219_);
lean_inc(v_defEqCtx_x3f_3218_);
lean_inc_ref(v_localInstances_3217_);
lean_inc_ref(v_lctx_3216_);
lean_inc(v_zetaDeltaSet_3215_);
v___x_3234_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v_zetaDeltaSet_3215_);
lean_ctor_set(v___x_3234_, 2, v_lctx_3216_);
lean_ctor_set(v___x_3234_, 3, v_localInstances_3217_);
lean_ctor_set(v___x_3234_, 4, v_defEqCtx_x3f_3218_);
lean_ctor_set(v___x_3234_, 5, v_synthPendingDepth_3219_);
lean_ctor_set(v___x_3234_, 6, v_canUnfold_x3f_3220_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*7, v_trackZetaDelta_3214_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*7 + 1, v_univApprox_3221_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3222_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*7 + 3, v_cacheInferType_3223_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
v___x_3235_ = lean_whnf(v_type_3186_, v___x_3234_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3265_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3265_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3265_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
if (lean_obj_tag(v_a_3236_) == 5)
{
lean_object* v_fn_3240_; lean_object* v_arg_3241_; lean_object* v___x_3242_; lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3260_; 
lean_del_object(v___x_3238_);
v_fn_3240_ = lean_ctor_get(v_a_3236_, 0);
lean_inc_ref(v_fn_3240_);
v_arg_3241_ = lean_ctor_get(v_a_3236_, 1);
lean_inc_ref(v_arg_3241_);
lean_dec_ref(v_a_3236_);
v___x_3242_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_fn_3240_, v_a_3188_);
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
lean_object* v___x_3247_; lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3259_; 
v___x_3247_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_arg_3241_, v_a_3188_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3259_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v_a_3243_);
lean_ctor_set(v___x_3252_, 1, v_a_3248_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set_tag(v___x_3245_, 1);
lean_ctor_set(v___x_3245_, 0, v___x_3252_);
v___x_3254_ = v___x_3245_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3256_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3254_);
v___x_3256_ = v___x_3250_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
lean_dec(v_a_3236_);
v___x_3261_ = lean_box(0);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3261_);
v___x_3263_ = v___x_3238_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
v_a_3266_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3235_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3235_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeApp_x3f___boxed(lean_object* v_type_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_isTypeApp_x3f(v_type_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp(lean_object* v_type_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Meta_isTypeApp_x3f(v_type_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3325_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3325_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3325_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
if (lean_obj_tag(v_a_3290_) == 1)
{
lean_object* v_val_3294_; lean_object* v_fst_3295_; lean_object* v___x_3296_; 
lean_del_object(v___x_3292_);
v_val_3294_ = lean_ctor_get(v_a_3290_, 0);
lean_inc(v_val_3294_);
lean_dec_ref(v_a_3290_);
v_fst_3295_ = lean_ctor_get(v_val_3294_, 0);
lean_inc(v_fst_3295_);
lean_dec(v_val_3294_);
v___x_3296_ = l_Lean_Meta_isMonad_x3f(v_fst_3295_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3311_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3311_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3311_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
if (lean_obj_tag(v_a_3297_) == 0)
{
uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3301_ = 0;
v___x_3302_ = lean_box(v___x_3301_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3302_);
v___x_3304_ = v___x_3299_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
else
{
uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
lean_dec_ref(v_a_3297_);
v___x_3306_ = 1;
v___x_3307_ = lean_box(v___x_3306_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3307_);
v___x_3309_ = v___x_3299_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
v_a_3312_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3296_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3296_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_dec(v_a_3290_);
v___x_3320_ = 0;
v___x_3321_ = lean_box(v___x_3320_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3321_);
v___x_3323_ = v___x_3292_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
v_a_3326_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3289_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3289_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonadApp___boxed(lean_object* v_type_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Meta_isMonadApp(v_type_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3340_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(lean_object* v_opts_3341_, lean_object* v_opt_3342_){
_start:
{
lean_object* v_name_3343_; lean_object* v_defValue_3344_; lean_object* v_map_3345_; lean_object* v___x_3346_; 
v_name_3343_ = lean_ctor_get(v_opt_3342_, 0);
v_defValue_3344_ = lean_ctor_get(v_opt_3342_, 1);
v_map_3345_ = lean_ctor_get(v_opts_3341_, 0);
v___x_3346_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3345_, v_name_3343_);
if (lean_obj_tag(v___x_3346_) == 0)
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_unbox(v_defValue_3344_);
return v___x_3347_;
}
else
{
lean_object* v_val_3348_; 
v_val_3348_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3348_);
lean_dec_ref(v___x_3346_);
if (lean_obj_tag(v_val_3348_) == 1)
{
uint8_t v_v_3349_; 
v_v_3349_ = lean_ctor_get_uint8(v_val_3348_, 0);
lean_dec_ref(v_val_3348_);
return v_v_3349_;
}
else
{
uint8_t v___x_3350_; 
lean_dec(v_val_3348_);
v___x_3350_ = lean_unbox(v_defValue_3344_);
return v___x_3350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(lean_object* v_opts_3351_, lean_object* v_opt_3352_){
_start:
{
uint8_t v_res_3353_; lean_object* v_r_3354_; 
v_res_3353_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_3351_, v_opt_3352_);
lean_dec_ref(v_opt_3352_);
lean_dec_ref(v_opts_3351_);
v_r_3354_ = lean_box(v_res_3353_);
return v_r_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0(lean_object* v_x_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0));
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec_ref(v_x_3365_);
return v_res_3371_;
}
}
static lean_object* _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l_Lean_mkBVar(v___x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f(lean_object* v_e_3394_, lean_object* v_expectedType_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___y_3402_; uint8_t v___y_3403_; lean_object* v_a_3408_; lean_object* v___y_3412_; lean_object* v___x_3422_; lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3826_; 
v___x_3422_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_expectedType_3395_, v_a_3397_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3826_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3826_;
goto v_resetjp_3424_;
}
v___jp_3401_:
{
if (v___y_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v___y_3402_);
v___x_3404_ = lean_box(0);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___y_3402_);
return v___x_3406_;
}
}
v___jp_3407_:
{
uint8_t v___x_3409_; 
v___x_3409_ = l_Lean_Exception_isInterrupt(v_a_3408_);
if (v___x_3409_ == 0)
{
uint8_t v___x_3410_; 
lean_inc_ref(v_a_3408_);
v___x_3410_ = l_Lean_Exception_isRuntime(v_a_3408_);
v___y_3402_ = v_a_3408_;
v___y_3403_ = v___x_3410_;
goto v___jp_3401_;
}
else
{
v___y_3402_ = v_a_3408_;
v___y_3403_ = v___x_3409_;
goto v___jp_3401_;
}
}
v___jp_3411_:
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3421_; 
v_a_3413_ = lean_ctor_get(v___y_3412_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___y_3412_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3415_ = v___y_3412_;
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___y_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3421_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_a_3417_; lean_object* v___x_3419_; 
v_a_3417_ = lean_ctor_get(v_a_3413_, 0);
lean_inc(v_a_3417_);
lean_dec(v_a_3413_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_a_3417_);
v___x_3419_ = v___x_3415_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; 
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
lean_inc_ref(v_e_3394_);
v___x_3427_ = lean_infer_type(v_e_3394_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3817_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(v_a_3428_, v_a_3397_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3817_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3817_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; 
lean_inc(v_a_3423_);
v___x_3434_ = l_Lean_Meta_isTypeApp_x3f(v_a_3423_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3808_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3808_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3808_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
if (lean_obj_tag(v_a_3435_) == 1)
{
lean_object* v_val_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3437_);
v_val_3439_ = lean_ctor_get(v_a_3435_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_a_3435_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3441_ = v_a_3435_;
v_isShared_3442_ = v_isSharedCheck_3803_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_val_3439_);
lean_dec(v_a_3435_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3803_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_fst_3443_; lean_object* v_snd_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3802_; 
v_fst_3443_ = lean_ctor_get(v_val_3439_, 0);
v_snd_3444_ = lean_ctor_get(v_val_3439_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_val_3439_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3446_ = v_val_3439_;
v_isShared_3447_ = v_isSharedCheck_3802_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snd_3444_);
lean_inc(v_fst_3443_);
lean_dec(v_val_3439_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3802_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; 
lean_inc(v_a_3430_);
v___x_3448_ = l_Lean_Meta_isTypeApp_x3f(v_a_3430_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3793_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3793_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3793_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
if (lean_obj_tag(v_a_3449_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3451_);
v_val_3453_ = lean_ctor_get(v_a_3449_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_a_3449_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3455_ = v_a_3449_;
v_isShared_3456_ = v_isSharedCheck_3788_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_val_3453_);
lean_dec(v_a_3449_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3788_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v_fst_3457_; lean_object* v_snd_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3787_; 
v_fst_3457_ = lean_ctor_get(v_val_3453_, 0);
v_snd_3458_ = lean_ctor_get(v_val_3453_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_val_3453_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3460_ = v_val_3453_;
v_isShared_3461_ = v_isSharedCheck_3787_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_snd_3458_);
lean_inc(v_fst_3457_);
lean_dec(v_val_3453_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3787_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Meta_saveState___redArg(v_a_3397_, v_a_3399_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
lean_inc(v_fst_3443_);
lean_inc(v_fst_3457_);
v___x_3464_ = l_Lean_Meta_isExprDefEq(v_fst_3457_, v_fst_3443_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3770_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3770_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3770_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_object* v_options_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
lean_dec(v_a_3463_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_del_object(v___x_3425_);
v_options_3470_ = lean_ctor_get(v_a_3398_, 2);
v___x_3471_ = l_Lean_Meta_autoLift;
v___x_3472_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_options_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3473_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3473_);
v___x_3475_ = v___x_3467_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
else
{
lean_object* v___x_3477_; 
lean_del_object(v___x_3467_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
lean_inc(v_fst_3457_);
v___x_3477_ = lean_infer_type(v_fst_3457_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
v___x_3479_ = lean_whnf(v_a_3478_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3479_);
if (lean_obj_tag(v_a_3480_) == 7)
{
lean_object* v_binderType_3481_; 
v_binderType_3481_ = lean_ctor_get(v_a_3480_, 1);
if (lean_obj_tag(v_binderType_3481_) == 3)
{
lean_object* v_body_3482_; 
v_body_3482_ = lean_ctor_get(v_a_3480_, 2);
if (lean_obj_tag(v_body_3482_) == 3)
{
lean_object* v_u_3483_; lean_object* v_u_3484_; lean_object* v___x_3485_; 
lean_inc_ref(v_body_3482_);
lean_inc_ref(v_binderType_3481_);
lean_dec_ref(v_a_3480_);
v_u_3483_ = lean_ctor_get(v_binderType_3481_, 0);
lean_inc(v_u_3483_);
lean_dec_ref(v_binderType_3481_);
v_u_3484_ = lean_ctor_get(v_body_3482_, 0);
lean_inc(v_u_3484_);
lean_dec_ref(v_body_3482_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
lean_inc(v_fst_3443_);
v___x_3485_ = lean_infer_type(v_fst_3443_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3485_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
v___x_3487_ = lean_whnf(v_a_3486_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3487_);
if (lean_obj_tag(v_a_3488_) == 7)
{
lean_object* v_binderType_3489_; 
v_binderType_3489_ = lean_ctor_get(v_a_3488_, 1);
if (lean_obj_tag(v_binderType_3489_) == 3)
{
lean_object* v_body_3490_; 
v_body_3490_ = lean_ctor_get(v_a_3488_, 2);
if (lean_obj_tag(v_body_3490_) == 3)
{
lean_object* v_u_3491_; lean_object* v_u_3492_; lean_object* v___x_3493_; 
lean_inc_ref(v_body_3490_);
lean_inc_ref(v_binderType_3489_);
lean_dec_ref(v_a_3488_);
v_u_3491_ = lean_ctor_get(v_binderType_3489_, 0);
lean_inc(v_u_3491_);
lean_dec_ref(v_binderType_3489_);
v_u_3492_ = lean_ctor_get(v_body_3490_, 0);
lean_inc(v_u_3492_);
lean_dec_ref(v_body_3490_);
v___x_3493_ = l_Lean_Meta_decLevel(v_u_3483_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = l_Lean_Meta_decLevel(v_u_3491_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref(v___x_3495_);
lean_inc(v_a_3494_);
v___x_3497_ = l_Lean_Meta_isLevelDefEq(v_a_3494_, v_a_3496_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3662_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3662_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3662_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_unbox(v_a_3498_);
lean_dec(v_a_3498_);
if (v___x_3502_ == 1)
{
lean_object* v___x_3503_; 
lean_del_object(v___x_3500_);
v___x_3503_ = l_Lean_Meta_decLevel(v_u_3484_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = l_Lean_Meta_decLevel(v_u_3492_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__1));
v___x_3508_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 1);
lean_ctor_set(v___x_3460_, 1, v___x_3508_);
lean_ctor_set(v___x_3460_, 0, v_a_3506_);
v___x_3510_ = v___x_3460_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3506_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 1);
lean_ctor_set(v___x_3446_, 1, v___x_3510_);
lean_ctor_set(v___x_3446_, 0, v_a_3504_);
v___x_3512_ = v___x_3446_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_a_3494_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = l_Lean_Expr_const___override(v___x_3507_, v___x_3513_);
v___x_3515_ = lean_unsigned_to_nat(2u);
v___x_3516_ = lean_mk_empty_array_with_capacity(v___x_3515_);
lean_inc(v_fst_3457_);
v___x_3517_ = lean_array_push(v___x_3516_, v_fst_3457_);
lean_inc(v_fst_3443_);
v___x_3518_ = lean_array_push(v___x_3517_, v_fst_3443_);
v___x_3519_ = l_Lean_mkAppN(v___x_3514_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = lean_box(0);
v___x_3521_ = l_Lean_Meta_trySynthInstance(v___x_3519_, v___x_3520_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3652_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3652_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3652_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; 
lean_del_object(v___x_3524_);
v_a_3526_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v_a_3522_);
lean_inc(v_snd_3458_);
v___x_3527_ = l_Lean_Meta_getDecLevel(v_snd_3458_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3529_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = l_Lean_Meta_getDecLevel(v_a_3430_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3529_);
lean_inc(v_a_3423_);
v___x_3531_ = l_Lean_Meta_getDecLevel(v_a_3423_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__3));
v___x_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_a_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3508_);
v___x_3535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_a_3530_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3528_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
lean_inc_ref(v___x_3536_);
v___x_3537_ = l_Lean_mkConst(v___x_3533_, v___x_3536_);
v___x_3538_ = lean_unsigned_to_nat(5u);
v___x_3539_ = lean_mk_empty_array_with_capacity(v___x_3538_);
lean_inc(v_fst_3457_);
v___x_3540_ = lean_array_push(v___x_3539_, v_fst_3457_);
lean_inc(v_fst_3443_);
v___x_3541_ = lean_array_push(v___x_3540_, v_fst_3443_);
lean_inc(v_a_3526_);
v___x_3542_ = lean_array_push(v___x_3541_, v_a_3526_);
lean_inc(v_snd_3458_);
v___x_3543_ = lean_array_push(v___x_3542_, v_snd_3458_);
lean_inc_ref(v_e_3394_);
v___x_3544_ = lean_array_push(v___x_3543_, v_e_3394_);
v___x_3545_ = l_Lean_mkAppN(v___x_3537_, v___x_3544_);
lean_dec_ref(v___x_3544_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = lean_infer_type(v___x_3545_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref(v___x_3546_);
lean_inc(v_a_3423_);
v___x_3548_ = l_Lean_Meta_isExprDefEq(v_a_3423_, v_a_3547_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3643_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3643_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3643_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_unbox(v_a_3549_);
lean_dec(v_a_3549_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_del_object(v___x_3551_);
lean_dec_ref(v___x_3545_);
lean_del_object(v___x_3455_);
lean_inc(v_fst_3443_);
v___x_3554_ = l_Lean_Meta_isMonad_x3f(v_fst_3443_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3635_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3635_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3635_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_val_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3631_; 
lean_del_object(v___x_3557_);
v_val_3559_ = lean_ctor_get(v_a_3555_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3561_ = v_a_3555_;
v_isShared_3562_ = v_isSharedCheck_3631_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_val_3559_);
lean_dec(v_a_3555_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3631_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; 
lean_inc(v_snd_3458_);
v___x_3563_ = l_Lean_Meta_getLevel(v_snd_3458_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v___x_3563_);
lean_inc(v_snd_3444_);
v___x_3565_ = l_Lean_Meta_getLevel(v_snd_3444_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__5));
v___x_3568_ = 0;
v___x_3569_ = ((lean_object*)(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1));
v___x_3570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_a_3566_);
lean_ctor_set(v___x_3570_, 1, v___x_3508_);
v___x_3571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_a_3564_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_mkConst(v___x_3569_, v___x_3571_);
v___x_3573_ = lean_obj_once(&l_Lean_Meta_coerceMonadLift_x3f___closed__6, &l_Lean_Meta_coerceMonadLift_x3f___closed__6_once, _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6);
v___x_3574_ = lean_unsigned_to_nat(3u);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___x_3574_);
lean_inc(v_snd_3458_);
v___x_3576_ = lean_array_push(v___x_3575_, v_snd_3458_);
v___x_3577_ = lean_array_push(v___x_3576_, v___x_3573_);
lean_inc(v_snd_3444_);
v___x_3578_ = lean_array_push(v___x_3577_, v_snd_3444_);
v___x_3579_ = l_Lean_mkAppN(v___x_3572_, v___x_3578_);
lean_dec_ref(v___x_3578_);
lean_inc(v_snd_3458_);
v___x_3580_ = l_Lean_mkForall(v___x_3567_, v___x_3568_, v_snd_3458_, v___x_3579_);
v___x_3581_ = l_Lean_Meta_trySynthInstance(v___x_3580_, v___x_3520_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3627_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3627_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3627_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
if (lean_obj_tag(v_a_3582_) == 1)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3584_);
v_a_3586_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v_a_3582_);
v___x_3587_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__9));
v___x_3588_ = l_Lean_mkConst(v___x_3587_, v___x_3536_);
v___x_3589_ = lean_unsigned_to_nat(8u);
v___x_3590_ = lean_mk_empty_array_with_capacity(v___x_3589_);
v___x_3591_ = lean_array_push(v___x_3590_, v_fst_3457_);
v___x_3592_ = lean_array_push(v___x_3591_, v_fst_3443_);
v___x_3593_ = lean_array_push(v___x_3592_, v_snd_3458_);
v___x_3594_ = lean_array_push(v___x_3593_, v_snd_3444_);
v___x_3595_ = lean_array_push(v___x_3594_, v_a_3526_);
v___x_3596_ = lean_array_push(v___x_3595_, v_a_3586_);
v___x_3597_ = lean_array_push(v___x_3596_, v_val_3559_);
v___x_3598_ = lean_array_push(v___x_3597_, v_e_3394_);
v___x_3599_ = l_Lean_mkAppN(v___x_3588_, v___x_3598_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = l_Lean_Meta_expandCoe(v___x_3599_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_fst_3602_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v_fst_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_fst_3602_);
lean_dec(v_a_3601_);
lean_inc(v_a_3399_);
lean_inc_ref(v_a_3398_);
lean_inc(v_a_3397_);
lean_inc_ref(v_a_3396_);
lean_inc(v_fst_3602_);
v___x_3603_ = lean_infer_type(v_fst_3602_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = l_Lean_Meta_isExprDefEq(v_a_3423_, v_a_3604_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3620_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_unbox(v_a_3606_);
lean_dec(v_a_3606_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v_fst_3602_);
lean_del_object(v___x_3561_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3520_);
v___x_3612_ = v___x_3608_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3520_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
else
{
lean_object* v___x_3615_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_fst_3602_);
v___x_3615_ = v___x_3561_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_fst_3602_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3615_);
v___x_3617_ = v___x_3608_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
else
{
lean_object* v_a_3621_; 
lean_dec(v_fst_3602_);
lean_del_object(v___x_3561_);
v_a_3621_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3605_);
v_a_3408_ = v_a_3621_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3622_; 
lean_dec(v_fst_3602_);
lean_del_object(v___x_3561_);
lean_dec(v_a_3423_);
v_a_3622_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3603_);
v_a_3408_ = v_a_3622_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3623_; 
lean_del_object(v___x_3561_);
lean_dec(v_a_3423_);
v_a_3623_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3600_);
v_a_3408_ = v_a_3623_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3625_; 
lean_dec(v_a_3582_);
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3520_);
v___x_3625_ = v___x_3584_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3520_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3628_; 
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3628_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3628_);
lean_dec_ref(v___x_3581_);
v_a_3408_ = v_a_3628_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3629_; 
lean_dec(v_a_3564_);
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3629_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3565_);
v_a_3408_ = v_a_3629_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3630_; 
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3630_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3563_);
v_a_3408_ = v_a_3630_;
goto v___jp_3407_;
}
}
}
else
{
lean_object* v___x_3633_; 
lean_dec(v_a_3555_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3520_);
v___x_3633_ = v___x_3557_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3520_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_object* v_a_3636_; 
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3636_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3554_);
v_a_3408_ = v_a_3636_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3545_);
v___x_3638_ = v___x_3455_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3545_);
v___x_3638_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3638_);
v___x_3640_ = v___x_3551_;
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
}
else
{
lean_object* v_a_3644_; 
lean_dec_ref(v___x_3545_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3644_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3548_);
v_a_3408_ = v_a_3644_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3645_; 
lean_dec_ref(v___x_3545_);
lean_dec_ref(v___x_3536_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3645_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3546_);
v_a_3408_ = v_a_3645_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3646_; 
lean_dec(v_a_3530_);
lean_dec(v_a_3528_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3646_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3531_);
v_a_3408_ = v_a_3646_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3647_; 
lean_dec(v_a_3528_);
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3647_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3647_);
lean_dec_ref(v___x_3529_);
v_a_3408_ = v_a_3647_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3648_; 
lean_dec(v_a_3526_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3648_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3648_);
lean_dec_ref(v___x_3527_);
v_a_3408_ = v_a_3648_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3650_; 
lean_dec(v_a_3522_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3520_);
v___x_3650_ = v___x_3524_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3520_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
else
{
lean_object* v_a_3653_; 
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3653_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3653_);
lean_dec_ref(v___x_3521_);
v_a_3408_ = v_a_3653_;
goto v___jp_3407_;
}
}
}
}
else
{
lean_object* v_a_3656_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3494_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3656_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3656_);
lean_dec_ref(v___x_3505_);
v_a_3408_ = v_a_3656_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3657_; 
lean_dec(v_a_3494_);
lean_dec(v_u_3492_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3657_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3503_);
v_a_3408_ = v_a_3657_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_dec(v_a_3494_);
lean_dec(v_u_3492_);
lean_dec(v_u_3484_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3658_ = lean_box(0);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3658_);
v___x_3660_ = v___x_3500_;
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
lean_object* v_a_3663_; 
lean_dec(v_a_3494_);
lean_dec(v_u_3492_);
lean_dec(v_u_3484_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3663_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3497_);
v_a_3408_ = v_a_3663_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3664_; 
lean_dec(v_a_3494_);
lean_dec(v_u_3492_);
lean_dec(v_u_3484_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3664_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3664_);
lean_dec_ref(v___x_3495_);
v_a_3408_ = v_a_3664_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3665_; 
lean_dec(v_u_3492_);
lean_dec(v_u_3491_);
lean_dec(v_u_3484_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3665_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3493_);
v_a_3408_ = v_a_3665_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3666_; 
lean_dec(v_u_3484_);
lean_dec(v_u_3483_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3666_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3488_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec_ref(v_a_3488_);
v___y_3412_ = v___x_3666_;
goto v___jp_3411_;
}
}
else
{
lean_object* v___x_3667_; 
lean_dec(v_u_3484_);
lean_dec(v_u_3483_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3667_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3488_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec_ref(v_a_3488_);
v___y_3412_ = v___x_3667_;
goto v___jp_3411_;
}
}
else
{
lean_object* v___x_3668_; 
lean_dec(v_u_3484_);
lean_dec(v_u_3483_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3668_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3488_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3488_);
v___y_3412_ = v___x_3668_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3669_; 
lean_dec(v_u_3484_);
lean_dec(v_u_3483_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3669_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3487_);
v_a_3408_ = v_a_3669_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3670_; 
lean_dec(v_u_3484_);
lean_dec(v_u_3483_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3670_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3485_);
v_a_3408_ = v_a_3670_;
goto v___jp_3407_;
}
}
else
{
lean_object* v___x_3671_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3671_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3480_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec_ref(v_a_3480_);
v___y_3412_ = v___x_3671_;
goto v___jp_3411_;
}
}
else
{
lean_object* v___x_3672_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3672_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3480_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec_ref(v_a_3480_);
v___y_3412_ = v___x_3672_;
goto v___jp_3411_;
}
}
else
{
lean_object* v___x_3673_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3673_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_3480_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3480_);
v___y_3412_ = v___x_3673_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3674_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3674_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3479_);
v_a_3408_ = v_a_3674_;
goto v___jp_3407_;
}
}
else
{
lean_object* v_a_3675_; 
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3675_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3675_);
lean_dec_ref(v___x_3477_);
v_a_3408_ = v_a_3675_;
goto v___jp_3407_;
}
}
}
else
{
lean_object* v___x_3676_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3460_);
lean_del_object(v___x_3446_);
lean_dec(v_a_3430_);
lean_dec(v_a_3423_);
v___x_3676_ = l_Lean_Meta_isMonad_x3f(v_fst_3443_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3769_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3769_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3769_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
if (lean_obj_tag(v_a_3677_) == 1)
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = ((lean_object*)(l_Lean_Meta_coerceMonadLift_x3f___closed__11));
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v_fst_3457_);
v___x_3683_ = v___x_3455_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_fst_3457_);
v___x_3683_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v_snd_3458_);
v___x_3685_ = v___x_3441_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_snd_3458_);
v___x_3685_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 0, v_snd_3444_);
v___x_3687_ = v___x_3432_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_snd_3444_);
v___x_3687_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; lean_object* v___y_3690_; uint8_t v___y_3691_; lean_object* v_a_3713_; lean_object* v___x_3717_; 
v___x_3688_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 1);
lean_ctor_set(v___x_3425_, 0, v_e_3394_);
v___x_3717_ = v___x_3425_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_e_3394_);
v___x_3717_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3716_;
}
v___jp_3689_:
{
if (v___y_3691_ == 0)
{
lean_object* v___x_3692_; 
lean_dec_ref(v___y_3690_);
lean_del_object(v___x_3679_);
v___x_3692_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3463_, v_a_3397_, v_a_3399_);
lean_dec(v_a_3463_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v___x_3692_, 0);
lean_dec(v_unused_3700_);
v___x_3694_ = v___x_3692_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v___x_3692_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3688_);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3688_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_a_3701_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3692_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3692_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
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
lean_object* v___x_3710_; 
lean_dec(v_a_3463_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 1);
lean_ctor_set(v___x_3679_, 0, v___y_3690_);
v___x_3710_ = v___x_3679_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___y_3690_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
v___jp_3712_:
{
uint8_t v___x_3714_; 
v___x_3714_ = l_Lean_Exception_isInterrupt(v_a_3713_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
lean_inc_ref(v_a_3713_);
v___x_3715_ = l_Lean_Exception_isRuntime(v_a_3713_);
v___y_3690_ = v_a_3713_;
v___y_3691_ = v___x_3715_;
goto v___jp_3689_;
}
else
{
v___y_3690_ = v_a_3713_;
v___y_3691_ = v___x_3714_;
goto v___jp_3689_;
}
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3718_ = lean_unsigned_to_nat(6u);
v___x_3719_ = lean_mk_empty_array_with_capacity(v___x_3718_);
v___x_3720_ = lean_array_push(v___x_3719_, v___x_3683_);
v___x_3721_ = lean_array_push(v___x_3720_, v___x_3685_);
v___x_3722_ = lean_array_push(v___x_3721_, v___x_3687_);
v___x_3723_ = lean_array_push(v___x_3722_, v___x_3688_);
v___x_3724_ = lean_array_push(v___x_3723_, v_a_3677_);
v___x_3725_ = lean_array_push(v___x_3724_, v___x_3717_);
v___x_3726_ = l_Lean_Meta_mkAppOptM(v___x_3681_, v___x_3725_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3745_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3745_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3745_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Meta_expandCoe(v_a_3727_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3743_; 
lean_del_object(v___x_3679_);
lean_dec(v_a_3463_);
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3743_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3743_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_fst_3736_; lean_object* v___x_3738_; 
v_fst_3736_ = lean_ctor_get(v_a_3732_, 0);
lean_inc(v_fst_3736_);
lean_dec(v_a_3732_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 1);
lean_ctor_set(v___x_3729_, 0, v_fst_3736_);
v___x_3738_ = v___x_3729_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_fst_3736_);
v___x_3738_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3738_);
v___x_3740_ = v___x_3734_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
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
else
{
lean_object* v_a_3744_; 
lean_del_object(v___x_3729_);
v_a_3744_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3744_);
lean_dec_ref(v___x_3731_);
v_a_3713_ = v_a_3744_;
goto v___jp_3712_;
}
}
}
else
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3746_);
lean_dec_ref(v___x_3726_);
v_a_3713_ = v_a_3746_;
goto v___jp_3712_;
}
}
}
}
}
}
else
{
lean_object* v___x_3751_; 
lean_del_object(v___x_3679_);
lean_dec(v_a_3677_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_del_object(v___x_3425_);
lean_dec_ref(v_e_3394_);
v___x_3751_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3463_, v_a_3397_, v_a_3399_);
lean_dec(v_a_3463_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3759_; 
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v___x_3751_, 0);
lean_dec(v_unused_3760_);
v___x_3753_ = v___x_3751_;
v_isShared_3754_ = v_isSharedCheck_3759_;
goto v_resetjp_3752_;
}
else
{
lean_dec(v___x_3751_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3759_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = lean_box(0);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3755_);
v___x_3757_ = v___x_3753_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_a_3761_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3751_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3751_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
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
}
}
else
{
lean_dec(v_a_3463_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3444_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_del_object(v___x_3425_);
lean_dec_ref(v_e_3394_);
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_a_3463_);
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3771_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3464_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3464_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
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
lean_del_object(v___x_3460_);
lean_dec(v_snd_3458_);
lean_dec(v_fst_3457_);
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3779_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3462_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3462_);
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
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec(v_a_3449_);
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3789_ = lean_box(0);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3789_);
v___x_3791_ = v___x_3451_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3446_);
lean_dec(v_snd_3444_);
lean_dec(v_fst_3443_);
lean_del_object(v___x_3441_);
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3794_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3448_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3448_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
lean_dec(v_a_3435_);
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v___x_3804_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3804_);
v___x_3806_ = v___x_3437_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3432_);
lean_dec(v_a_3430_);
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3809_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3434_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3434_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3425_);
lean_dec(v_a_3423_);
lean_dec_ref(v_e_3394_);
v_a_3818_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3427_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3427_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceMonadLift_x3f___boxed(lean_object* v_e_3827_, lean_object* v_expectedType_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_Meta_coerceMonadLift_x3f(v_e_3827_, v_expectedType_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f(lean_object* v_expr_3835_, lean_object* v_expectedType_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3842_; 
lean_inc_ref(v_expectedType_3836_);
lean_inc_ref(v_expr_3835_);
v___x_3842_ = l_Lean_Meta_coerceMonadLift_x3f(v_expr_3835_, v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3922_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3922_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3922_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
if (lean_obj_tag(v_a_3843_) == 1)
{
lean_object* v_val_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_val_3847_ = lean_ctor_get(v_a_3843_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_a_3843_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3849_ = v_a_3843_;
v_isShared_3850_ = v_isSharedCheck_3859_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_val_3847_);
lean_dec(v_a_3843_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3859_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3851_ = lean_box(0);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v_val_3847_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3852_);
v___x_3854_ = v___x_3849_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3854_);
v___x_3856_ = v___x_3845_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v___x_3860_; 
lean_del_object(v___x_3845_);
lean_dec(v_a_3843_);
lean_inc_ref(v_expectedType_3836_);
v___x_3860_ = l_Lean_Meta_whnfR(v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; uint8_t v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
v___x_3862_ = l_Lean_Expr_isForall(v_a_3861_);
lean_dec(v_a_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3835_, v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
return v___x_3863_;
}
else
{
lean_object* v___x_3864_; 
lean_inc_ref(v_expr_3835_);
v___x_3864_ = l_Lean_Meta_coerceToFunction_x3f(v_expr_3835_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v___x_3864_);
if (lean_obj_tag(v_a_3865_) == 1)
{
lean_object* v_val_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3904_; 
v_val_3866_ = lean_ctor_get(v_a_3865_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_a_3865_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3868_ = v_a_3865_;
v_isShared_3869_ = v_isSharedCheck_3904_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_val_3866_);
lean_dec(v_a_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3904_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; 
lean_inc(v_a_3840_);
lean_inc_ref(v_a_3839_);
lean_inc(v_a_3838_);
lean_inc_ref(v_a_3837_);
lean_inc(v_val_3866_);
v___x_3870_ = lean_infer_type(v_val_3866_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
lean_inc_ref(v_expectedType_3836_);
v___x_3872_ = l_Lean_Meta_isExprDefEq(v_a_3871_, v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3887_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3887_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3887_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_unbox(v_a_3873_);
lean_dec(v_a_3873_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_del_object(v___x_3875_);
lean_del_object(v___x_3868_);
lean_dec(v_val_3866_);
v___x_3878_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3835_, v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_val_3866_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3880_);
v___x_3882_ = v___x_3868_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3882_);
v___x_3884_ = v___x_3875_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_del_object(v___x_3868_);
lean_dec(v_val_3866_);
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_a_3888_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3872_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3872_);
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
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_del_object(v___x_3868_);
lean_dec(v_val_3866_);
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_a_3896_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3870_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3870_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
else
{
lean_object* v___x_3905_; 
lean_dec(v_a_3865_);
v___x_3905_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(v_expr_3835_, v_expectedType_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
return v___x_3905_;
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_a_3906_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3864_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3864_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_a_3914_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3860_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3860_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_expectedType_3836_);
lean_dec_ref(v_expr_3835_);
v_a_3923_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3842_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3842_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerceCollectingNames_x3f___boxed(lean_object* v_expr_3931_, lean_object* v_expectedType_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3931_, v_expectedType_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f(lean_object* v_expr_3939_, lean_object* v_expectedType_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_Meta_coerceCollectingNames_x3f(v_expr_3939_, v_expectedType_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3971_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3971_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3971_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
switch(lean_obj_tag(v_a_3947_))
{
case 0:
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_box(0);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3951_);
v___x_3953_ = v___x_3949_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
case 1:
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3966_; 
v_a_3955_ = lean_ctor_get(v_a_3947_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_a_3947_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3957_ = v_a_3947_;
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v_a_3947_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v_fst_3959_; lean_object* v___x_3961_; 
v_fst_3959_ = lean_ctor_get(v_a_3955_, 0);
lean_inc(v_fst_3959_);
lean_dec(v_a_3955_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v_fst_3959_);
v___x_3961_ = v___x_3957_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_fst_3959_);
v___x_3961_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3963_; 
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3961_);
v___x_3963_ = v___x_3949_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
default: 
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_box(2);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3967_);
v___x_3969_ = v___x_3949_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
v_a_3972_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3946_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3946_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_coerce_x3f___boxed(lean_object* v_expr_3980_, lean_object* v_expectedType_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_coerce_x3f(v_expr_3980_, v_expectedType_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3987_;
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
